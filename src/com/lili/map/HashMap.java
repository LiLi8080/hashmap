package com.lili.map;

/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package java.util;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.*;
import java.util.AbstractMap;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

public class HashMap<K,V> extends AbstractMap<K,V>
        implements java.util.Map<K,V>, Cloneable, Serializable {

    private static final long serialVersionUID = 362498820763181265L;

    // 缺省时table的大小 即缺省时Node数组的长度
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16
    // table的最大长度  即hash表中Node数组的最大长度
    static final int MAXIMUM_CAPACITY = 1 << 30;
    // 缺省时负载因子的大小 即没有调用构造函数给负载因子赋值
    static final float DEFAULT_LOAD_FACTOR = 0.75f;
    // 树化域值 即当Node数组中某个链表中元素数量大于8时可能进行树化
    static final int TREEIFY_THRESHOLD = 8;
    // 树降级域值 即Node数组中某个链表中元素个数小于6时将对树进行链表化
    static final int UNTREEIFY_THRESHOLD = 6;
    // 树化的另一个域值 当hash表中所有元素个数大于64才可能对某个大于8个元素的链表树化
    static final int MIN_TREEIFY_CAPACITY = 64;


    /* Field */
    // hash表
    transient java.util.HashMap.Node<K,V>[] table;
    transient Set<Entry<K,V>> entrySet;
    // 当前hash表中元素个数
    transient int size;
    // 当前hash表结构修改次数  往hash表中增加/删除某个元素代表结构修改 但替换某个元素不算
    transient int modCount;
    // 扩容域指，当hash表中元素个数超过域值时触发扩容。
    int threshold;
    // 负载因子 threshold = loadFactor*capacity  capacity是hash表中Node数组长度
    final float loadFactor;


    /*  构造方法源码分析   */
    public HashMap(int initialCapacity, float loadFactor) {
        // 就是做了一些校验
        // capacity必须>0且<=MAXIMUM_CAPACITY 当输入capacity小于时抛出异常
        // 大于MAXIMUM_CAPACITY时直接初始化为MAXIMUM_CAPACITY
        if (initialCapacity < 0)
            throw new IllegalArgumentException("Illegal initial capacity: " +
                    initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)
            initialCapacity = MAXIMUM_CAPACITY;
        // loadFactor必须>0的数 否则抛异常
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new IllegalArgumentException("Illegal load factor: " +
                    loadFactor);

        this.loadFactor = loadFactor;
        // hash表中Node数组的长度必须是2^x，但传入的initialCapacity不一定是2^x 因此需要tableSizeFor去处理
        this.threshold = tableSizeFor(initialCapacity);
    }
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }
    public HashMap() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }
    public HashMap(java.util.Map<? extends K, ? extends V> m) {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }
    /*
     * 作用：返回一个>=当前cap的一个数字 ，并且这个数字一定是一个2的次方数
     *
     * 示例：
     *      cap = 10
     *      n = 10-1 = 9
     *      0b1001 | 0b0100 => 0b1101
     *      0b1101 | 0b0011 => 0b1111
     *      0b1111 | 0b0000 => 0b1111
     *      0b1111 | 0b0000 => 0b1111
     *      0b1111 | 0b0000 => 0b1111 = 15
     *
     *      return n+1 = 15+1 = 16 = 2^4
     *
     * 实际意义：
     *      将某个cap = 0001 1101 1100 ==> 0001 1111 1111 +1 = 0010 0000 0000
     *      return 0010 0000 0000  这个数一定是>= cap的2的次方数
     */
    static final int tableSizeFor(int cap) {
        int n = cap - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }


    /*  put源码分析 */
    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }
    /*
     * 作用： 让key的hash值的高16位也参与运算 即hash扰动函数
     *       当key为null时，hash（key) =0 ，路由算法查询在哈希表Node数组位置也为0，因此key=null的数据将插在hash表Node[0]的链表中
     * 如果不用扰乱函数 ，每次路由只有末尾n位参与有效运算
     */
    static final int hash(Object key) {
        int h;
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }
    /*
     * onlyIfAbsent : =true时，如果散列表中有此key的数据，则不进行插入操作
     *                =false时，散列表中有此数据则进行替换
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent,
                   boolean evict) {
        // tab:引用当前hashMap的散列表
        // p:表示当前散列表的元素
        // n:表示散列表数组的长度
        // i:表示路由寻址结果
        java.util.HashMap.Node<K,V>[] tab;
        java.util.HashMap.Node<K,V> p;
        int n, i;

        // 延迟初始化，第一次putVal才会初始化hashMap对象中最耗费内存的散列表
        if ((tab = table) == null || (n = tab.length) == 0)
            n = (tab = resize()).length;

        // i = (n - 1) & hash  路由算法 i=路由找到的hash列表Node数组的下标
        // 即要将当前元素p插入到Node[i]中
        // 情况一：Node[i] == null 直接插入
        if ((p = tab[i = (n - 1) & hash]) == null)
            tab[i] = newNode(hash, key, value, null);

            // 情况二： Node[i]！=null
        else {
            // e: 不为null表示找到了一个与当前要插入的key-value一致的key的元素
            // k: 表示临时的一个key
            java.util.HashMap.Node<K,V> e; K k;

            // 表示桶位中的该元素与你当前插入的元素的key完全一致，表示后续需要进行替换操作
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                e = p;

                // 是红黑树时....
            else if (p instanceof java.util.HashMap.TreeNode)
                e = ((java.util.HashMap.TreeNode<K,V>)p).putTreeVal(this, tab, hash, key, value);

                // 是链表时xxx
            else {
                // 链表的头元素与我们要插入的元素的key不一致
                for (int binCount = 0; ; ++binCount) {
                    // 条件成立说明迭代到最后一个元素也没找到与你要插入的元素key相同的元素
                    // 需要将插入元素插入到当前链表末尾
                    if ((e = p.next) == null) {
                        p.next = newNode(hash, key, value, null);
                        // 当前链表有8个元素 再插入一个元素需要进行树化
                        if (binCount >= TREEIFY_THRESHOLD - 1) // -1 for 1st
                            treeifyBin(tab, hash);
                        break;
                    }

                    // 条件成立：说明找到与要插入元素相同的key的node，需要进行替换操作
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        break;

                    p = e;
                }
            }

            // e!=null说明找到了相同key的node 需要进行替换
            if (e != null) { // existing mapping for key
                V oldValue = e.value;
                if (!onlyIfAbsent || oldValue == null)
                    e.value = value;
                afterNodeAccess(e);
                return oldValue;  //  替换完后直接返回
            }
        }

        // 表示元素进行的是插入而不是替换操作  即替换操作modCount不+1
        ++modCount;
        // 插入新元素size++，如果自增后元素值大于threshold则进行扩容操作
        if (++size > threshold)
            resize();
        afterNodeInsertion(evict);
        return null;
    }


    /* resize源码分析 */
    /*
     * 作用：扩容操作。为了解决h哈希冲突d导致的链化y影响查询效率的问题，扩容后会缓解该问题
     */
    final java.util.HashMap.Node<K,V>[] resize() {
        // 引用扩容前的hash表
        java.util.HashMap.Node<K,V>[] oldTab = table;
        // 表示扩容之前table数组的长度
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        // oldThr：表示扩容之前的扩容域指，触发本次扩容的域指
        int oldThr = threshold;
        // newCap: 扩容之后table数组的大小
        // newThr：扩容之后下次再次触发k扩容的条件
        int newCap, newThr = 0;

        // 计算newCap 和 newThr
        // 条件成立：说明hashMap中的散列表已经初始化过了，这是一次正常扩容
        if (oldCap > 0) {
            // 扩容之前的table数组大小已经达到了最大值，不扩容
            if (oldCap >= MAXIMUM_CAPACITY) {
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            // oldCap左移一位s实现数值翻倍，并赋值给newCap newCapx小于数组最大值限制q且扩容之前的域值>=16
            // 这种情况下 下次扩容的域指等于当前阈值翻倍
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY &&
                    oldCap >= DEFAULT_INITIAL_CAPACITY)
                newThr = oldThr << 1; // double threshold
        }

        // oldCap == 0 说明hashmap的散列表是null
        // 1. new HahMap(initCap,loadFactor)
        // 2. new HashMap(initCap)
        // 3. new HashMap(map) 会更改oldThr的值
        // 4. new HashMap() 不会更改oldThr的
        // 第一次初始化 置newCap = oldThr 因为oldThr是通过tableSizeFor(cap）计算所得 一定为2的N次方
        else if (oldThr > 0)
            newCap = oldThr;

        // oldCap == 0 && oldThr == 0
        // new HashMap() 构造对象 只初始化loadFactor
        else {
            newCap = DEFAULT_INITIAL_CAPACITY;  // 16
            newThr = (int)(DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);  // 12
        }

        // newThr为零时，通过newCaph和loadFactor计算出一个newThr
        if (newThr == 0) {
            float ft = (float)newCap * loadFactor;
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float)MAXIMUM_CAPACITY ?
                    (int)ft : Integer.MAX_VALUE);
        }
        threshold = newThr;



        // 根据newCap创建新的更大的数组
        @SuppressWarnings({"rawtypes","unchecked"})
        java.util.HashMap.Node<K,V>[] newTab = (java.util.HashMap.Node<K,V>[])new java.util.HashMap.Node[newCap];
        table = newTab;

        // 说明扩容前table中可能有数据
        if (oldTab != null) {
            for (int j = 0; j < oldCap; ++j) {
                // 当前node节点
                java.util.HashMap.Node<K,V> e;
                // 说明当前桶中有数据，但数据具体是单个数据 / 链表/红黑树不确定
                if ((e = oldTab[j]) != null) {
                    // 方便JVM GC回收内存
                    oldTab[j] = null;

                    //  第一种情况：当前桶中只有一个元素，从未发生过碰撞，则直接计算出当前元素应该存放再新table中的位置
                    //  然后扔进去
                    if (e.next == null)
                        newTab[e.hash & (newCap - 1)] = e;

                    // 第二种情况 当前节点已经树化 ...
                    else if (e instanceof java.util.HashMap.TreeNode)
                        ((java.util.HashMap.TreeNode<K,V>)e).split(this, newTab, j, oldCap);

                    // 第三种情况 已经形成链表
                    else {
                        // 低位链表：存放扩容之后的数组的下标位置，与当前s数组的下标位置相同
                        java.util.HashMap.Node<K,V> loHead = null, loTail = null;
                        // 高位链表：存放扩容之后的数组的下标位置为当前数组的下标位置+扩容之前数组的长度
                        java.util.HashMap.Node<K,V> hiHead = null, hiTail = null;
                        java.util.HashMap.Node<K,V> next;
                        do {
                            next = e.next;
                            // oldIndex = e.hash & （oldCap-1) 当e.hash & oldCap == 0 证明e.hash在oldCap的最高位为0 转换成新数组的下标将无变化
                            if ((e.hash & oldCap) == 0) {
                                if (loTail == null)
                                    loHead = e;
                                else
                                    loTail.next = e;
                                loTail = e;
                            }
                            // oldIndex = e.hash & （oldCap-1) 当e.hash & oldCap == 1 证明e.hash在oldCap的最高位为1 转换成新数组的下标将增加oldCap
                            else {
                                if (hiTail == null)
                                    hiHead = e;
                                else
                                    hiTail.next = e;
                                hiTail = e;
                            }
                        } while ((e = next) != null);
                        if (loTail != null) {
                            loTail.next = null;
                            newTab[j] = loHead;
                        }
                        if (hiTail != null) {
                            hiTail.next = null;
                            newTab[j + oldCap] = hiHead;
                        }
                    }
                }
            }
        }
        return newTab;
    }


    /* get源码分析 */
    public V get(Object key) {
        java.util.HashMap.Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? null : e.value;
    }
    final java.util.HashMap.Node<K,V> getNode(int hash, Object key) {
        // tab: 当前散列表
        // first：桶中首元素
        // e: 临时存放node 的元素
        // n : 当前散列表数组长度
        java.util.HashMap.Node<K,V>[] tab; java.util.HashMap.Node<K,V> first, e; int n; K k;


        // 条件满足： 散列表不为空 且路由到的桶中有元素
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (first = tab[(n - 1) & hash]) != null) {

            // 桶中首元素即为要查找的元素
            if (first.hash == hash &&
                    ((k = first.key) == key || (key != null && key.equals(k))))
                return first;

            // 桶中元素不只一个
            if ((e = first.next) != null) {
                // 桶中元素已形成树结构 查找树
                if (first instanceof java.util.HashMap.TreeNode)
                    return ((java.util.HashMap.TreeNode<K,V>)first).getTreeNode(hash, key);
                // 桶中元素是链表结构 遍历链表
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        return e;
                } while ((e = e.next) != null);
            }
        }

        // 散列表为空或路由到的桶中无元素或位查找到对应元素
        return null;
    }

    /* remove 源码分析 */
    public V remove(Object key) {
        java.util.HashMap.Node<K,V> e;
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
                null : e.value;
    }
    @Override
    public boolean remove(Object key, Object value) {
        return removeNode(hash(key), key, value, true, true) != null;
    }
    final java.util.HashMap.Node<K,V> removeNode(int hash, Object key, Object value,
                                                 boolean matchValue, boolean movable) {
        // tab: 当前散列表
        // p： 当前node元素
        // n: 散列表数组长度
        // index:寻址结果 即寻址到的桶位
        java.util.HashMap.Node<K,V>[] tab; java.util.HashMap.Node<K,V> p; int n, index;

        // 条件为真： 哈希表不为空 且查找到的桶位有数据
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (p = tab[index = (n - 1) & hash]) != null) {

            java.util.HashMap.Node<K,V> node = null, e; K k; V v;
            // 第一种情况： 当前桶的首元素即为要删除的元素 用node标记
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                node = p;

            // 第二种情况 ： 当前桶首元素不是要删除的元素，桶中不只一个元素
            else if ((e = p.next) != null) {
                // 当前桶为红黑树 利用红黑树方法获取删除node
                if (p instanceof java.util.HashMap.TreeNode)
                    node = ((java.util.HashMap.TreeNode<K,V>)p).getTreeNode(hash, key);

                // 档期桶为链表 遍历链表查找要删除的元素并用node标记
                else {
                    do {
                        if (e.hash == hash &&
                                ((k = e.key) == key ||
                                        (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }

            // node标记不为空 即查找到了要删除的元素
            if (node != null && (!matchValue || (v = node.value) == value ||
                    (value != null && value.equals(v)))) {
                // 要删除的元素在红黑树中 利用红黑树方法删除
                if (node instanceof java.util.HashMap.TreeNode)
                    ((java.util.HashMap.TreeNode<K,V>)node).removeTreeNode(this, tab, movable);
                // 要删除的元素是桶中链表的首元素
                else if (node == p)
                    tab[index] = node.next;
                // 要删除的元素是桶中链表的中间元素
                else
                    p.next = node.next;
                ++modCount;  //删除操作也要更新modCount
                --size;
                afterNodeRemoval(node);
                return node; // 返回删除的元素
            }
        }
        return null;
    }


    /* replace源码分析 */
    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        java.util.HashMap.Node<K,V> e; V v;
        if ((e = getNode(hash(key), key)) != null &&
                ((v = e.value) == oldValue || (v != null && v.equals(oldValue)))) {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }
    @Override
    public V replace(K key, V value) {
        java.util.HashMap.Node<K,V> e;
        if ((e = getNode(hash(key), key)) != null) {
            V oldValue = e.value;
            e.value = value;
            afterNodeAccess(e);
            return oldValue;
        }
        return null;
    }

    static class Node<K,V> implements java.util.Map.Entry<K,V> {
        final int hash;
        final K key;
        V value;
        java.util.HashMap.Node<K,V> next;

        Node(int hash, K key, V value, java.util.HashMap.Node<K,V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }


        public final K getKey()        { return key; }
        public final V getValue()      { return value; }
        public final String toString() { return key + "=" + value; }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof java.util.Map.Entry) {
                java.util.Map.Entry<?,?> e = (java.util.Map.Entry<?,?>)o;
                if (Objects.equals(key, e.getKey()) &&
                        Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }
    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c; Type[] ts, as; Type t; ParameterizedType p;
            if ((c = x.getClass()) == String.class) // bypass checks
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {
                for (int i = 0; i < ts.length; ++i) {
                    if (((t = ts[i]) instanceof ParameterizedType) &&
                            ((p = (ParameterizedType)t).getRawType() ==
                                    Comparable.class) &&
                            (as = p.getActualTypeArguments()) != null &&
                            as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        return null;
    }
    @SuppressWarnings({"rawtypes","unchecked"}) // for cast to Comparable
    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable)k).compareTo(x));
    }
    final void putMapEntries(java.util.Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();
        if (s > 0) {
            if (table == null) { // pre-size
                float ft = ((float)s / loadFactor) + 1.0F;
                int t = ((ft < (float)MAXIMUM_CAPACITY) ?
                        (int)ft : MAXIMUM_CAPACITY);
                if (t > threshold)
                    threshold = tableSizeFor(t);
            }
            else if (s > threshold)
                resize();
            for (java.util.Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }
    public int size() {
        return size;
    }
    public boolean isEmpty() {
        return size == 0;
    }
    public boolean containsKey(Object key) {
        return getNode(hash(key), key) != null;
    }
    @Override
    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }
    final void treeifyBin(java.util.HashMap.Node<K,V>[] tab, int hash) {
        int n, index; java.util.HashMap.Node<K,V> e;
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            resize();
        else if ((e = tab[index = (n - 1) & hash]) != null) {
            java.util.HashMap.TreeNode<K,V> hd = null, tl = null;
            do {
                java.util.HashMap.TreeNode<K,V> p = replacementTreeNode(e, null);
                if (tl == null)
                    hd = p;
                else {
                    p.prev = tl;
                    tl.next = p;
                }
                tl = p;
            } while ((e = e.next) != null);
            if ((tab[index] = hd) != null)
                hd.treeify(tab);
        }
    }
    public void putAll(java.util.Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }
    public void clear() {
        java.util.HashMap.Node<K,V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0) {
            size = 0;
            for (int i = 0; i < tab.length; ++i)
                tab[i] = null;
        }
    }
    public boolean containsValue(Object value) {
        java.util.HashMap.Node<K,V>[] tab; V v;
        if ((tab = table) != null && size > 0) {
            for (int i = 0; i < tab.length; ++i) {
                for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next) {
                    if ((v = e.value) == value ||
                            (value != null && value.equals(v)))
                        return true;
                }
            }
        }
        return false;
    }
    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new java.util.HashMap.KeySet();
            keySet = ks;
        }
        return ks;
    }
    final class KeySet extends AbstractSet<K> {
        public final int size()                 { return size; }
        public final void clear()               { java.util.HashMap.this.clear(); }
        public final Iterator<K> iterator()     { return new java.util.HashMap.KeyIterator(); }
        public final boolean contains(Object o) { return containsKey(o); }
        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }
        public final Spliterator<K> spliterator() {
            return new java.util.HashMap.KeySpliterator<>(java.util.HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super K> action) {
            java.util.HashMap.Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.key);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }
    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new java.util.HashMap.Values();
            values = vs;
        }
        return vs;
    }
    final class Values extends AbstractCollection<V> {
        public final int size()                 { return size; }
        public final void clear()               { java.util.HashMap.this.clear(); }
        public final Iterator<V> iterator()     { return new java.util.HashMap.ValueIterator(); }
        public final boolean contains(Object o) { return containsValue(o); }
        public final Spliterator<V> spliterator() {
            return new java.util.HashMap.ValueSpliterator<>(java.util.HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super V> action) {
            java.util.HashMap.Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.value);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }
    public Set<java.util.Map.Entry<K,V>> entrySet() {
        Set<java.util.Map.Entry<K,V>> es;
        return (es = entrySet) == null ? (entrySet = new java.util.HashMap.EntrySet()) : es;
    }
    final class EntrySet extends AbstractSet<java.util.Map.Entry<K,V>> {
        public final int size()                 { return size; }
        public final void clear()               { java.util.HashMap.this.clear(); }
        public final Iterator<java.util.Map.Entry<K,V>> iterator() {
            return new java.util.HashMap.EntryIterator();
        }
        public final boolean contains(Object o) {
            if (!(o instanceof java.util.Map.Entry))
                return false;
            java.util.Map.Entry<?,?> e = (java.util.Map.Entry<?,?>) o;
            Object key = e.getKey();
            java.util.HashMap.Node<K,V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }
        public final boolean remove(Object o) {
            if (o instanceof java.util.Map.Entry) {
                java.util.Map.Entry<?,?> e = (java.util.Map.Entry<?,?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }
        public final Spliterator<java.util.Map.Entry<K,V>> spliterator() {
            return new java.util.HashMap.EntrySpliterator<>(java.util.HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super java.util.Map.Entry<K,V>> action) {
            java.util.HashMap.Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }
    @Override
    public V getOrDefault(Object key, V defaultValue) {
        java.util.HashMap.Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }
    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        java.util.HashMap.Node<K,V>[] tab; java.util.HashMap.Node<K,V> first; int n, i;
        int binCount = 0;
        java.util.HashMap.TreeNode<K,V> t = null;
        java.util.HashMap.Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof java.util.HashMap.TreeNode)
                old = (t = (java.util.HashMap.TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                java.util.HashMap.Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null) {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null) {
            return null;
        } else if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        else if (t != null)
            t.putTreeVal(this, tab, hash, key, v);
        else {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1)
                treeifyBin(tab, hash);
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }
    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        java.util.HashMap.Node<K,V> e; V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
                (oldValue = e.value) != null) {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null) {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
            else
                removeNode(hash, key, null, false, true);
        }
        return null;
    }
    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        java.util.HashMap.Node<K,V>[] tab; java.util.HashMap.Node<K,V> first; int n, i;
        int binCount = 0;
        java.util.HashMap.TreeNode<K,V> t = null;
        java.util.HashMap.Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof java.util.HashMap.TreeNode)
                old = (t = (java.util.HashMap.TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                java.util.HashMap.Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
        }
        else if (v != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, v);
            else {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }
    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null)
            throw new NullPointerException();
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        java.util.HashMap.Node<K,V>[] tab; java.util.HashMap.Node<K,V> first; int n, i;
        int binCount = 0;
        java.util.HashMap.TreeNode<K,V> t = null;
        java.util.HashMap.Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof java.util.HashMap.TreeNode)
                old = (t = (java.util.HashMap.TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                java.util.HashMap.Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null) {
            V v;
            if (old.value != null)
                v = remappingFunction.apply(old.value, value);
            else
                v = value;
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
            return v;
        }
        if (value != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, value);
            else {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }
    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        java.util.HashMap.Node<K,V>[] tab;
        if (action == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next)
                    action.accept(e.key, e.value);
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }
    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        java.util.HashMap.Node<K,V>[] tab;
        if (function == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next) {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }
    @Override
    public Object clone() {
        java.util.HashMap<K,V> result;
        try {
            result = (java.util.HashMap<K,V>)super.clone();
        } catch (CloneNotSupportedException e) {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();
        result.putMapEntries(this, false);
        return result;
    }
    final float loadFactor() { return loadFactor; }
    final int capacity() {
        return (table != null) ? table.length :
                (threshold > 0) ? threshold :
                        DEFAULT_INITIAL_CAPACITY;
    }
    private void writeObject(java.io.ObjectOutputStream s)
            throws IOException {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }
    private void readObject(java.io.ObjectInputStream s)
            throws IOException, ClassNotFoundException {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new InvalidObjectException("Illegal load factor: " +
                    loadFactor);
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                    mappings);
        else if (mappings > 0) { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float)mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                    DEFAULT_INITIAL_CAPACITY :
                    (fc >= MAXIMUM_CAPACITY) ?
                            MAXIMUM_CAPACITY :
                            tableSizeFor((int)fc));
            float ft = (float)cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                    (int)ft : Integer.MAX_VALUE);
            @SuppressWarnings({"rawtypes","unchecked"})
            java.util.HashMap.Node<K,V>[] tab = (java.util.HashMap.Node<K,V>[])new java.util.HashMap.Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++) {
                @SuppressWarnings("unchecked")
                K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }
    abstract class HashIterator {
        java.util.HashMap.Node<K,V> next;        // next entry to return
        java.util.HashMap.Node<K,V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            java.util.HashMap.Node<K,V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {} while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final java.util.HashMap.Node<K,V> nextNode() {
            java.util.HashMap.Node<K,V>[] t;
            java.util.HashMap.Node<K,V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {} while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            java.util.HashMap.Node<K,V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }
    final class KeyIterator extends java.util.HashMap.HashIterator
            implements Iterator<K> {
        public final K next() { return nextNode().key; }
    }
    final class ValueIterator extends java.util.HashMap.HashIterator
            implements Iterator<V> {
        public final V next() { return nextNode().value; }
    }
    final class EntryIterator extends java.util.HashMap.HashIterator
            implements Iterator<java.util.Map.Entry<K,V>> {
        public final java.util.Map.Entry<K,V> next() { return nextNode(); }
    }
    static class HashMapSpliterator<K,V> {
        final java.util.HashMap<K,V> map;
        java.util.HashMap.Node<K,V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(java.util.HashMap<K,V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                java.util.HashMap<K,V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                java.util.HashMap.Node<K,V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }
    static final class KeySpliterator<K,V>
            extends java.util.HashMap.HashMapSpliterator<K,V>
            implements Spliterator<K> {
        KeySpliterator(java.util.HashMap<K,V> m, int origin, int fence, int est,
                       int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public java.util.HashMap.KeySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new java.util.HashMap.KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap<K,V> m = map;
            java.util.HashMap.Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                java.util.HashMap.Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super K> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap.Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }
    static final class ValueSpliterator<K,V>
            extends java.util.HashMap.HashMapSpliterator<K,V>
            implements Spliterator<V> {
        ValueSpliterator(java.util.HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public java.util.HashMap.ValueSpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new java.util.HashMap.ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap<K,V> m = map;
            java.util.HashMap.Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                java.util.HashMap.Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super V> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap.Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }
    static final class EntrySpliterator<K,V>
            extends java.util.HashMap.HashMapSpliterator<K,V>
            implements Spliterator<java.util.Map.Entry<K,V>> {
        EntrySpliterator(java.util.HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public java.util.HashMap.EntrySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new java.util.HashMap.EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super java.util.Map.Entry<K,V>> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap<K,V> m = map;
            java.util.HashMap.Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                java.util.HashMap.Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            java.util.HashMap.Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        java.util.HashMap.Node<K,V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }
    java.util.HashMap.Node<K,V> newNode(int hash, K key, V value, java.util.HashMap.Node<K,V> next) {
        return new java.util.HashMap.Node<>(hash, key, value, next);
    }
    java.util.HashMap.Node<K,V> replacementNode(java.util.HashMap.Node<K,V> p, java.util.HashMap.Node<K,V> next) {
        return new java.util.HashMap.Node<>(p.hash, p.key, p.value, next);
    }
    java.util.HashMap.TreeNode<K,V> newTreeNode(int hash, K key, V value, java.util.HashMap.Node<K,V> next) {
        return new java.util.HashMap.TreeNode<>(hash, key, value, next);
    }
    java.util.HashMap.TreeNode<K,V> replacementTreeNode(java.util.HashMap.Node<K,V> p, java.util.HashMap.Node<K,V> next) {
        return new java.util.HashMap.TreeNode<>(p.hash, p.key, p.value, next);
    }
    void reinitialize() {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }
    void afterNodeAccess(java.util.HashMap.Node<K,V> p) { }
    void afterNodeInsertion(boolean evict) { }
    void afterNodeRemoval(java.util.HashMap.Node<K,V> p) { }
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        java.util.HashMap.Node<K,V>[] tab;
        if (size > 0 && (tab = table) != null) {
            for (int i = 0; i < tab.length; ++i) {
                for (java.util.HashMap.Node<K,V> e = tab[i]; e != null; e = e.next) {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }
    static final class TreeNode<K,V> extends LinkedHashMap.Entry<K,V> {
        java.util.HashMap.TreeNode<K,V> parent;  // red-black tree links
        java.util.HashMap.TreeNode<K,V> left;
        java.util.HashMap.TreeNode<K,V> right;
        java.util.HashMap.TreeNode<K,V> prev;    // needed to unlink next upon deletion
        boolean red;
        TreeNode(int hash, K key, V val, java.util.HashMap.Node<K,V> next) {
            super(hash, key, val, next);
        }


        final java.util.HashMap.TreeNode<K,V> root() {
            for (java.util.HashMap.TreeNode<K,V> r = this, p;;) {
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }


        static <K,V> void moveRootToFront(java.util.HashMap.Node<K,V>[] tab, java.util.HashMap.TreeNode<K,V> root) {
            int n;
            if (root != null && tab != null && (n = tab.length) > 0) {
                int index = (n - 1) & root.hash;
                java.util.HashMap.TreeNode<K,V> first = (java.util.HashMap.TreeNode<K,V>)tab[index];
                if (root != first) {
                    java.util.HashMap.Node<K,V> rn;
                    tab[index] = root;
                    java.util.HashMap.TreeNode<K,V> rp = root.prev;
                    if ((rn = root.next) != null)
                        ((java.util.HashMap.TreeNode<K,V>)rn).prev = rp;
                    if (rp != null)
                        rp.next = rn;
                    if (first != null)
                        first.prev = root;
                    root.next = first;
                    root.prev = null;
                }
                assert checkInvariants(root);
            }
        }


        final java.util.HashMap.TreeNode<K,V> find(int h, Object k, Class<?> kc) {
            java.util.HashMap.TreeNode<K,V> p = this;
            do {
                int ph, dir; K pk;
                java.util.HashMap.TreeNode<K,V> pl = p.left, pr = p.right, q;
                if ((ph = p.hash) > h)
                    p = pl;
                else if (ph < h)
                    p = pr;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                else if (pl == null)
                    p = pr;
                else if (pr == null)
                    p = pl;
                else if ((kc != null ||
                        (kc = comparableClassFor(k)) != null) &&
                        (dir = compareComparables(kc, k, pk)) != 0)
                    p = (dir < 0) ? pl : pr;
                else if ((q = pr.find(h, k, kc)) != null)
                    return q;
                else
                    p = pl;
            } while (p != null);
            return null;
        }


        final java.util.HashMap.TreeNode<K,V> getTreeNode(int h, Object k) {
            return ((parent != null) ? root() : this).find(h, k, null);
        }
        static int tieBreakOrder(Object a, Object b) {
            int d;
            if (a == null || b == null ||
                    (d = a.getClass().getName().
                            compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ?
                        -1 : 1);
            return d;
        }


        final void treeify(java.util.HashMap.Node<K,V>[] tab) {
            java.util.HashMap.TreeNode<K,V> root = null;
            for (java.util.HashMap.TreeNode<K,V> x = this, next; x != null; x = next) {
                next = (java.util.HashMap.TreeNode<K,V>)x.next;
                x.left = x.right = null;
                if (root == null) {
                    x.parent = null;
                    x.red = false;
                    root = x;
                }
                else {
                    K k = x.key;
                    int h = x.hash;
                    Class<?> kc = null;
                    for (java.util.HashMap.TreeNode<K,V> p = root;;) {
                        int dir, ph;
                        K pk = p.key;
                        if ((ph = p.hash) > h)
                            dir = -1;
                        else if (ph < h)
                            dir = 1;
                        else if ((kc == null &&
                                (kc = comparableClassFor(k)) == null) ||
                                (dir = compareComparables(kc, k, pk)) == 0)
                            dir = tieBreakOrder(k, pk);

                        java.util.HashMap.TreeNode<K,V> xp = p;
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            x.parent = xp;
                            if (dir <= 0)
                                xp.left = x;
                            else
                                xp.right = x;
                            root = balanceInsertion(root, x);
                            break;
                        }
                    }
                }
            }
            moveRootToFront(tab, root);
        }


        final java.util.HashMap.Node<K,V> untreeify(java.util.HashMap<K,V> map) {
            java.util.HashMap.Node<K,V> hd = null, tl = null;
            for (java.util.HashMap.Node<K,V> q = this; q != null; q = q.next) {
                java.util.HashMap.Node<K,V> p = map.replacementNode(q, null);
                if (tl == null)
                    hd = p;
                else
                    tl.next = p;
                tl = p;
            }
            return hd;
        }


        final java.util.HashMap.TreeNode<K,V> putTreeVal(java.util.HashMap<K,V> map, java.util.HashMap.Node<K,V>[] tab,
                                                         int h, K k, V v) {
            Class<?> kc = null;
            boolean searched = false;
            java.util.HashMap.TreeNode<K,V> root = (parent != null) ? root() : this;
            for (java.util.HashMap.TreeNode<K,V> p = root;;) {
                int dir, ph; K pk;
                if ((ph = p.hash) > h)
                    dir = -1;
                else if (ph < h)
                    dir = 1;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                else if ((kc == null &&
                        (kc = comparableClassFor(k)) == null) ||
                        (dir = compareComparables(kc, k, pk)) == 0) {
                    if (!searched) {
                        java.util.HashMap.TreeNode<K,V> q, ch;
                        searched = true;
                        if (((ch = p.left) != null &&
                                (q = ch.find(h, k, kc)) != null) ||
                                ((ch = p.right) != null &&
                                        (q = ch.find(h, k, kc)) != null))
                            return q;
                    }
                    dir = tieBreakOrder(k, pk);
                }

                java.util.HashMap.TreeNode<K,V> xp = p;
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    java.util.HashMap.Node<K,V> xpn = xp.next;
                    java.util.HashMap.TreeNode<K,V> x = map.newTreeNode(h, k, v, xpn);
                    if (dir <= 0)
                        xp.left = x;
                    else
                        xp.right = x;
                    xp.next = x;
                    x.parent = x.prev = xp;
                    if (xpn != null)
                        ((java.util.HashMap.TreeNode<K,V>)xpn).prev = x;
                    moveRootToFront(tab, balanceInsertion(root, x));
                    return null;
                }
            }
        }


        final void removeTreeNode(java.util.HashMap<K,V> map, java.util.HashMap.Node<K,V>[] tab,
                                  boolean movable) {
            int n;
            if (tab == null || (n = tab.length) == 0)
                return;
            int index = (n - 1) & hash;
            java.util.HashMap.TreeNode<K,V> first = (java.util.HashMap.TreeNode<K,V>)tab[index], root = first, rl;
            java.util.HashMap.TreeNode<K,V> succ = (java.util.HashMap.TreeNode<K,V>)next, pred = prev;
            if (pred == null)
                tab[index] = first = succ;
            else
                pred.next = succ;
            if (succ != null)
                succ.prev = pred;
            if (first == null)
                return;
            if (root.parent != null)
                root = root.root();
            if (root == null || root.right == null ||
                    (rl = root.left) == null || rl.left == null) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            java.util.HashMap.TreeNode<K,V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null) {
                java.util.HashMap.TreeNode<K,V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red; s.red = p.red; p.red = c; // swap colors
                java.util.HashMap.TreeNode<K,V> sr = s.right;
                java.util.HashMap.TreeNode<K,V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else {
                    java.util.HashMap.TreeNode<K,V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p) {
                java.util.HashMap.TreeNode<K,V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            java.util.HashMap.TreeNode<K,V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p) {  // detach
                java.util.HashMap.TreeNode<K,V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        final void split(java.util.HashMap<K,V> map, java.util.HashMap.Node<K,V>[] tab, int index, int bit) {
            java.util.HashMap.TreeNode<K,V> b = this;
            // Relink into lo and hi lists, preserving order
            java.util.HashMap.TreeNode<K,V> loHead = null, loTail = null;
            java.util.HashMap.TreeNode<K,V> hiHead = null, hiTail = null;
            int lc = 0, hc = 0;
            for (java.util.HashMap.TreeNode<K,V> e = b, next; e != null; e = next) {
                next = (java.util.HashMap.TreeNode<K,V>)e.next;
                e.next = null;
                if ((e.hash & bit) == 0) {
                    if ((e.prev = loTail) == null)
                        loHead = e;
                    else
                        loTail.next = e;
                    loTail = e;
                    ++lc;
                }
                else {
                    if ((e.prev = hiTail) == null)
                        hiHead = e;
                    else
                        hiTail.next = e;
                    hiTail = e;
                    ++hc;
                }
            }

            if (loHead != null) {
                if (lc <= UNTREEIFY_THRESHOLD)
                    tab[index] = loHead.untreeify(map);
                else {
                    tab[index] = loHead;
                    if (hiHead != null) // (else is already treeified)
                        loHead.treeify(tab);
                }
            }
            if (hiHead != null) {
                if (hc <= UNTREEIFY_THRESHOLD)
                    tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead;
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }



        static <K,V> java.util.HashMap.TreeNode<K,V> rotateLeft(java.util.HashMap.TreeNode<K,V> root,
                                                                java.util.HashMap.TreeNode<K,V> p) {
            java.util.HashMap.TreeNode<K,V> r, pp, rl;
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K,V> java.util.HashMap.TreeNode<K,V> rotateRight(java.util.HashMap.TreeNode<K,V> root,
                                                                 java.util.HashMap.TreeNode<K,V> p) {
            java.util.HashMap.TreeNode<K,V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static <K,V> java.util.HashMap.TreeNode<K,V> balanceInsertion(java.util.HashMap.TreeNode<K,V> root,
                                                                      java.util.HashMap.TreeNode<K,V> x) {
            x.red = true;
            for (java.util.HashMap.TreeNode<K,V> xp, xpp, xppl, xppr;;) {
                if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (!xp.red || (xpp = xp.parent) == null)
                    return root;
                if (xp == (xppl = xpp.left)) {
                    if ((xppr = xpp.right) != null && xppr.red) {
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.right) {
                            root = rotateLeft(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                }
                else {
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        static <K,V> java.util.HashMap.TreeNode<K,V> balanceDeletion(java.util.HashMap.TreeNode<K,V> root,
                                                                     java.util.HashMap.TreeNode<K,V> x) {
            for (java.util.HashMap.TreeNode<K,V> xp, xpl, xpr;;)  {
                if (x == null || x == root)
                    return root;
                else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (x.red) {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else {
                        java.util.HashMap.TreeNode<K,V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                                (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }
                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                        null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else {
                        java.util.HashMap.TreeNode<K,V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                                (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        }
                        else {
                            if (sl == null || !sl.red) {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                        null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }
        static <K,V> boolean checkInvariants(java.util.HashMap.TreeNode<K,V> t) {
            java.util.HashMap.TreeNode<K,V> tp = t.parent, tl = t.left, tr = t.right,
                    tb = t.prev, tn = (java.util.HashMap.TreeNode<K,V>)t.next;
            if (tb != null && tb.next != t)
                return false;
            if (tn != null && tn.prev != t)
                return false;
            if (tp != null && t != tp.left && t != tp.right)
                return false;
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            if (tl != null && !checkInvariants(tl))
                return false;
            if (tr != null && !checkInvariants(tr))
                return false;
            return true;
        }
    }

}
