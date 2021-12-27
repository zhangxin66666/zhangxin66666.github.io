
#1.成员变量
```java
//散列表数组的最大限制
private static final int MAXIMUM_CAPACITY = 1 << 30;

//散列表默认值
private static final int DEFAULT_CAPACITY = 16;


static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;

//并发级别：jdk7历史遗留问题，仅仅在初始化的时候使用到，并不是真正的代表并发级别
private static final int DEFAULT_CONCURRENCY_LEVEL = 16;

//负载因子，JDK1.8中 ConcurrentHashMap 是固定值
private static final float LOAD_FACTOR = 0.75f;

//树化阈值，指定桶位 链表长度达到8的话，有可能发生树化操作。
static final int TREEIFY_THRESHOLD = 8;

//红黑树转化为链表的阈值
static final int UNTREEIFY_THRESHOLD = 6;

//联合TREEIFY_THRESHOLD控制桶位是否树化，只有当table数组长度达到64且 某个桶位 中的链表长度达到8，才会真正树化
static final int MIN_TREEIFY_CAPACITY = 64;

//线程迁移数据最小步长，控制线程迁移任务最小区间一个值
private static final int MIN_TRANSFER_STRIDE = 16;


//计算扩容时候生成的一个 标识戳
private static int RESIZE_STAMP_BITS = 16;

//结果是65535 表示并发扩容最多线程数
private static final int MAX_RESIZERS = (1 << (32 - RESIZE_STAMP_BITS)) - 1;

//扩容相关
private static  final int RESIZE_STAMP_SHIFT = 32 - RESIZE_STAMP_BITS;

//当node节点hash=-1 表示当前节点已经被迁移了  ，fwd节点
static final int MOVED     = -1; // hash for forwarding nodes

//node hash=-2 表示当前节点已经树化 且 当前节点为treebin对象  ，代理操作红黑树
static final int TREEBIN   = -2; // hash for roots of trees

static final int RESERVED  = -3; // hash for transient reservations
//转化成二进制实际上是 31个 1  可以将一个负数通过位移运算得到一个正数

static final int HASH_BITS = 0x7fffffff; // usable bits of normal node hash

//当前系统的cpu数量
static final int NCPU = Runtime.getRuntime().availableProcessors();

//为了兼容7版本的chp保存的，核心代码并没有使用到
private static final ObjectStreamField[] serialPersistentFields = {
        new ObjectStreamField("segments", Segment[].class),
        new ObjectStreamField("segmentMask", Integer.TYPE),
        new ObjectStreamField("segmentShift", Integer.TYPE)
        };

//散列表，长度一定是2次方数
transient volatile Node<K,V>[] table;

//扩容过程中，会将扩容中的新table 赋值给nextTable 保持引用，扩容结束之后，这里会被设置为Null
private transient volatile Node<K,V>[] nextTable;

//LongAdder 中的 baseCount 未发生竞争时 或者 当前LongAdder处于加锁状态时，增量累到到baseCount中
private transient volatile long baseCount;

/**
 * sizeCtl < 0
 * 1. -1 表示当前table正在初始化（有线程在创建table数组），当前线程需要自旋等待..
 * 2.表示当前table数组正在进行扩容 ,高16位表示：扩容的标识戳   低16位表示：（1 + nThread） 当前参与并发扩容的线程数量
 *
 * sizeCtl = 0，表示创建table数组时 使用DEFAULT_CAPACITY为大小
 *
 * sizeCtl > 0
 *
 * 1. 如果table未初始化，表示初始化大小
 * 2. 如果table已经初始化，表示下次扩容时的 触发条件（阈值）
 */
private transient volatile int sizeCtl;

/**
 *
 * 扩容过程中，记录当前进度。所有线程都需要从transferIndex中分配区间任务，去执行自己的任务。
 */
private transient volatile int transferIndex;

/**
 * LongAdder中的cellsBuzy 0表示当前LongAdder对象无锁状态，1表示当前LongAdder对象加锁状态
 */
private transient volatile int cellsBusy;

/**
 * LongAdder中的cells数组，当baseCount发生竞争后，会创建cells数组，
 * 线程会通过计算hash值 取到 自己的cell ，将增量累加到指定cell中
 * 总数 = sum(cells) + baseCount
 */
private transient volatile CounterCell[] counterCells;

// Unsafe mechanics
private static final sun.misc.Unsafe U;
/**表示sizeCtl属性在ConcurrentHashMap中内存偏移地址*/
private static final long SIZECTL;
/**表示transferIndex属性在ConcurrentHashMap中内存偏移地址*/
private static final long TRANSFERINDEX;
/**表示baseCount属性在ConcurrentHashMap中内存偏移地址*/
private static final long BASECOUNT;
/**表示cellsBusy属性在ConcurrentHashMap中内存偏移地址*/
private static final long CELLSBUSY;
/**表示cellValue属性在CounterCell中内存偏移地址*/
private static final long CELLVALUE;
/**表示数组第一个元素的偏移地址*/
private static final long ABASE;
private static final int ASHIFT;

static {
        try {
        U = sun.misc.Unsafe.getUnsafe();
        Class<?> k = ConcurrentHashMap.class;
        SIZECTL = U.objectFieldOffset
                (k.getDeclaredField("sizeCtl"));
                TRANSFERINDEX = U.objectFieldOffset
                (k.getDeclaredField("transferIndex"));
                BASECOUNT = U.objectFieldOffset
                (k.getDeclaredField("baseCount"));
                CELLSBUSY = U.objectFieldOffset
                (k.getDeclaredField("cellsBusy"));
                Class<?> ck = CounterCell.class;
        CELLVALUE = U.objectFieldOffset
                (ck.getDeclaredField("value"));
                Class<?> ak = Node[].class;
        ABASE = U.arrayBaseOffset(ak);
                //表示数组单元所占用空间大小,scale 表示Node[]数组中每一个单元所占用空间大小
                int scale = U.arrayIndexScale(ak);
                //1 0000 & 0 1111 = 0
                if ((scale & (scale - 1)) != 0)
                throw new Error("data type scale not a power of two");
                //numberOfLeadingZeros() 这个方法是返回当前数值转换为二进制后，从高位到低位开始统计，看有多少个0连续在一块。
                //8 => 1000 numberOfLeadingZeros(8) = 28
                //4 => 100 numberOfLeadingZeros(4) = 29
                //ASHIFT = 31 - 29 = 2 ？？
                //ABASE + （5 << ASHIFT）
                ASHIFT = 31 - Integer.numberOfLeadingZeros(scale);
                } catch (Exception e) {
                throw new Error(e);
                }
                }
```

#2.基础方法
##2.1 spread
高位运算
```java
static final int spread(int h) {
    return (h ^ (h >>> 16)) & HASH_BITS;
}
```
##2.2 tabAt
该方法获取对象中offset偏移地址对应的对象field的值。实际上这段代码的含义等价于tab[i],但是为什么不直接使用 tab[i]来计算呢？

getObjectVolatile，一旦看到 volatile 关键字，就表示可见性。因为对 volatile 写操作 happen-before 于 volatile 读操作，因此其他线程对 table 的修改均对 get 读取可见；

虽然 table 数组本身是增加了 volatile 属性，但是“volatile 的数组只针对数组的引用具有volatile 的语义，而不是它的元素”。 所以如果有其他线程对这个数组的元素进行写操作，那么当前线程来读的时候不一定能读到最新的值。出于性能考虑，Doug Lea 直接通过 Unsafe 类来对 table 进行操作。

![img.png](./img/tabAt.png)
```java
static final <K,V> Node<K,V> tabAt(Node<K,V>[] tab, int i) {
    return (Node<K,V>)U.getObjectVolatile(tab, ((long)i << ASHIFT) + ABASE);
}
```
##2.3 casTabAt
cas设置当前节点为桶位的头节点
```java
static final <K,V> boolean casTabAt(Node<K,V>[] tab, int i,
                                    Node<K,V> c, Node<K,V> v) {
    return U.compareAndSwapObject(tab, ((long)i << ASHIFT) + ABASE, c, v);
}
```
##2.4 setTabAt
```java
static final <K,V> void setTabAt(Node<K,V>[] tab, int i, Node<K,V> v) {
    U.putObjectVolatile(tab, ((long)i << ASHIFT) + ABASE, v);
}
```
##2.5 resizeStamp
resizeStamp 用来生成一个和扩容有关的扩容戳，具体有什么作用呢？
```java
static final int resizeStamp(int n) {
    return Integer.numberOfLeadingZeros(n) | (1 << (RESIZE_STAMP_BITS - 1));
}
```
Integer.numberOfLeadingZeros 这个方法是返回无符号整数 n 最高位非 0 位前面的 0 的个数。

比如 10 的二进制是 0000 0000 0000 0000 0000 0000 0000 1010，那么这个方法返回的值就是 28。

根据 resizeStamp 的运算逻辑，我们来推演一下，假如 n=16，那么 resizeStamp(16)=32796转化为二进制是[0000 0000 0000 0000 1000 0000 0001 1100]

接着再来看,当第一个线程尝试进行扩容的时候，会执行下面这段代码：

```U.compareAndSwapInt(this, SIZECTL, sc, (rs << RESIZE_STAMP_SHIFT) + 2)```
rs 左移 16 位，相当于原本的二进制低位变成了高位 1000 0000 0001 1100 0000 0000 00000000

然后再+2 =1000 0000 0001 1100 0000 0000 0000 0000+10=1000 0000 0001 1100 0000 00000000 0010

**高 16 位代表扩容的标记、低 16 位代表并行扩容的线程数**

这样来存储有什么好处呢？

1，首先在 CHM 中是支持并发扩容的，也就是说如果当前的数组需要进行扩容操作，可以由多个线程来共同负责

2，可以保证每次扩容都生成唯一的生成戳，每次新的扩容，都有一个不同的 n，这个生成戳就是根据 n 来计算出来的一个数字，n 不同，这个数字也不同

第一个线程尝试扩容的时候，为什么是+2

因为 1 表示初始化，2 表示一个线程在执行扩容，而且对 sizeCtl 的操作都是基于位运算的，所以不会关心它本身的数值是多少，只关心它在二进制上的数值，而 sc + 1 会在低 16 位上加 1。
##2.6 tableSizeFor
经过多次位移返回大于等于c的最小的二次方数
```java
    /**
     * Returns a power of two table size for the given desired capacity.
     * See Hackers Delight, sec 3.2
     * 返回>=c的最小的2的次方数
     * c=28
     * n=27 => 0b 11011
     * 11011 | 01101 => 11111
     * 11111 | 00111 => 11111
     * ....
     * => 11111 + 1 =100000 = 32
     */
private static final int tableSizeFor(int c) {
    int n = c - 1;
    n |= n >>> 1;
    n |= n >>> 2;
    n |= n >>> 4;
    n |= n >>> 8;
    n |= n >>> 16;
    return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
}
```
#3. 构造方法
```java
public ConcurrentHashMap() {
}

public ConcurrentHashMap(int initialCapacity) {
    if (initialCapacity < 0)
        throw new IllegalArgumentException();
    //如果指定的容量超过允许的最大值，设置为最大值
    int cap = ((initialCapacity >= (MAXIMUM_CAPACITY >>> 1)) ?
               MAXIMUM_CAPACITY :
               tableSizeFor(initialCapacity + (initialCapacity >>> 1) + 1));
    /**
         * sizeCtl > 0
         * 当目前table未初始化时，sizeCtl表示初始化容量
         */
    this.sizeCtl = cap;
}

public ConcurrentHashMap(Map<? extends K, ? extends V> m) {
    this.sizeCtl = DEFAULT_CAPACITY;
    putAll(m);
}


public ConcurrentHashMap(int initialCapacity, float loadFactor) {
    this(initialCapacity, loadFactor, 1);
}


public ConcurrentHashMap(int initialCapacity,
                         float loadFactor, int concurrencyLevel) {
    //参数校验
    if (!(loadFactor > 0.0f) || initialCapacity < 0 || concurrencyLevel <= 0)
        throw new IllegalArgumentException();
    //如果初始容量小于并发级别，那就设置初始容量为并发级别
    if (initialCapacity < concurrencyLevel)   
        initialCapacity = concurrencyLevel;   
    //16/0.75 +1 = 22
    long size = (long)(1.0 + (long)initialCapacity / loadFactor);
    // 22 - > 32
    int cap = (size >= (long)MAXIMUM_CAPACITY) ?
        MAXIMUM_CAPACITY : tableSizeFor((int)size);
    /**
         * sizeCtl > 0
         * 当目前table未初始化时，sizeCtl表示初始化容量
         */
    this.sizeCtl = cap;
}
```
#4.put
```java
public V put(K key, V value) {
    //如果key已经存在，是否覆盖，默认是false
    return putVal(key, value, false);
}
```
#5 putVal
```java
final V putVal(K key, V value, boolean onlyIfAbsent) {
    //控制k 和 v 不能为null
    if (key == null || value == null) throw new NullPointerException();

    //通过spread方法，可以让高位也能参与进寻址运算。
    int hash = spread(key.hashCode());
    //binCount表示当前k-v 封装成node后插入到指定桶位后，在桶位中的所属链表的下标位置
    //0 表示当前桶位为null，node可以直接放着
    //2 表示当前桶位已经可能是红黑树
    int binCount = 0;

    //tab 引用map对象的table
    //自旋
    for (Node<K,V>[] tab = table;;) {
        //f 表示桶位的头结点
        //n 表示散列表数组的长度
        //i 表示key通过寻址计算后，得到的桶位下标
        //fh 表示桶位头结点的hash值
        Node<K,V> f; int n, i, fh;

        //CASE1：成立，表示当前map中的table尚未初始化..
        if (tab == null || (n = tab.length) == 0)
            //最终当前线程都会获取到最新的map.table引用。
            tab = initTable();
        //CASE2：i 表示key使用路由寻址算法得到 key对应 table数组的下标位置，tabAt 获取指定桶位的头结点 f
        else if ((f = tabAt(tab, i = (n - 1) & hash)) == null) {
            //进入到CASE2代码块 前置条件 当前table数组i桶位是Null时。
            //使用CAS方式 设置 指定数组i桶位 为 new Node<K,V>(hash, key, value, null),并且期望值是null
            //cas操作成功 表示ok，直接break for循环即可
            //cas操作失败，表示在当前线程之前，有其它线程先你一步向指定i桶位设置值了。
            //当前线程只能再次自旋，去走其它逻辑。
            if (casTabAt(tab, i, null,
                         new Node<K,V>(hash, key, value, null)))
                break;                   // no lock when adding to empty bin
        }

        //CASE3：前置条件，桶位的头结点一定不是null。
        //条件成立表示当前桶位的头结点 为 FWD结点，表示目前map正处于扩容过程中..
        else if ((fh = f.hash) == MOVED)
            //看到fwd节点后，当前节点有义务帮助当前map对象完成迁移数据的工作
            //帮助扩容
            tab = helpTransfer(tab, f);

        //CASE4：当前桶位 可能是 链表 也可能是 红黑树代理结点TreeBin
        else {
            //当插入key存在时，会将旧值赋值给oldVal，返回给put方法调用处..
            V oldVal = null;

            //使用sync 加锁“头节点”，理论上是“头结点”
            synchronized (f) {
                //为什么又要对比一下，看看当前桶位的头节点 是否为 之前获取的头结点？
                //为了避免其它线程将该桶位的头结点修改掉，导致当前线程从sync 加锁 就有问题了。之后所有操作都不用在做了。
                if (tabAt(tab, i) == f) {//条件成立，说明咱们 加锁 的对象没有问题，可以进来造了！

                    //条件成立，说明当前桶位就是普通链表桶位。
                    if (fh >= 0) {
                        //1.当前插入key与链表当中所有元素的key都不一致时，当前的插入操作是追加到链表的末尾，binCount表示链表长度
                        //2.当前插入key与链表当中的某个元素的key一致时，当前插入操作可能就是替换了。binCount表示冲突位置（binCount - 1）
                        binCount = 1;

                        //迭代循环当前桶位的链表，e是每次循环处理节点。
                        for (Node<K,V> e = f;; ++binCount) {
                            //当前循环节点 key
                            K ek;
                            //条件一：e.hash == hash 成立 表示循环的当前元素的hash值与插入节点的hash值一致，需要进一步判断
                            //条件二：((ek = e.key) == key ||(ek != null && key.equals(ek)))
                            //       成立：说明循环的当前节点与插入节点的key一致，发生冲突了
                            if (e.hash == hash &&
                                ((ek = e.key) == key ||
                                 (ek != null && key.equals(ek)))) {
                                //将当前循环的元素的 值 赋值给oldVal
                                oldVal = e.val;

                                if (!onlyIfAbsent)
                                    e.val = value;
                                break;
                            }
                            //当前元素 与 插入元素的key不一致 时，会走下面程序。
                            //1.更新循环处理节点为 当前节点的下一个节点
                            //2.判断下一个节点是否为null，如果是null，说明当前节点已经是队尾了，插入数据需要追加到队尾节点的后面。

                            Node<K,V> pred = e;
                            if ((e = e.next) == null) {
                                pred.next = new Node<K,V>(hash, key,
                                                          value, null);
                                break;
                            }
                        }
                    }
                    //前置条件，该桶位一定不是链表
                    //条件成立，表示当前桶位是 红黑树代理结点TreeBin
                    else if (f instanceof TreeBin) {
                        //p 表示红黑树中如果与你插入节点的key 有冲突节点的话 ，则putTreeVal 方法 会返回冲突节点的引用。
                        Node<K,V> p;
                        //强制设置binCount为2，因为binCount <= 1 时有其它含义，所以这里设置为了2 
                        binCount = 2;

                        //条件一：成立，说明当前插入节点的key与红黑树中的某个节点的key一致，冲突了
                        if ((p = ((TreeBin<K,V>)f).putTreeVal(hash, key,
                                                              value)) != null) {
                            //将冲突节点的值 赋值给 oldVal
                            oldVal = p.val;
                            if (!onlyIfAbsent)
                                p.val = value;
                        }
                    }
                }
            }

            //说明当前桶位不为null，可能是红黑树 也可能是链表
            if (binCount != 0) {
                //如果binCount>=8 表示处理的桶位一定是链表
                if (binCount >= TREEIFY_THRESHOLD)
                    //调用转化链表为红黑树的方法
                    treeifyBin(tab, i);
                //说明当前线程插入的数据key，与原有k-v发生冲突，需要将原数据v返回给调用者。
                if (oldVal != null)
                    return oldVal;
                break;
            }
        }
    }

    //1.统计当前table一共有多少数据
    //2.判断是否达到扩容阈值标准，触发扩容。
    addCount(1L, binCount);

    return null;
}
```
#6 initTable
数组初始化方法，这个方法比较简单，就是初始化一个合适大小的数组。

sizeCtl ：这个标志是在 Node 数组初始化或者扩容的时候的一个控制位标识，负数代表正在进行初始化或者扩容操作。

-1 代表正在初始化

-N 代表有 N-1 个线程正在进行扩容操作，这里不是简单的理解成 n 个线程，sizeCtl 就是-N

0 标识 Node 数组还没有被初始化，正数代表初始化或者下一次扩容的大小
```java
/**
     * Initializes table, using the size recorded in sizeCtl.
     *      * sizeCtl < 0
     *      * 1. -1 表示当前table正在初始化（有线程在创建table数组），当前线程需要自旋等待..
     *      * 2.表示当前table数组正在进行扩容 ,高16位表示：扩容的标识戳   低16位表示：（1 + nThread） 当前参与并发扩容的线程数量
     *      *
     *      * sizeCtl = 0，表示创建table数组时 使用DEFAULT_CAPACITY为大小
     *      *
     *      * sizeCtl > 0
     *      *
     *      * 1. 如果table未初始化，表示初始化大小
     *      * 2. 如果table已经初始化，表示下次扩容时的 触发条件（阈值）
     */
private final Node<K,V>[] initTable() {
    //tab 引用map.table
    //sc sizeCtl的临时值
    Node<K,V>[] tab; int sc;
    //自旋 条件：map.table 尚未初始化
    while ((tab = table) == null || tab.length == 0) {

        if ((sc = sizeCtl) < 0)
            //大概率就是-1，表示其它线程正在进行创建table的过程，当前线程没有竞争到初始化table的锁。
            Thread.yield(); // lost initialization race; just spin

        //1.sizeCtl = 0，表示创建table数组时 使用DEFAULT_CAPACITY为大小
        //2.如果table未初始化，表示初始化大小
        //3.如果table已经初始化，表示下次扩容时的 触发条件（阈值）
        else if (U.compareAndSwapInt(this, SIZECTL, sc, -1)) {
            try {
                //这里为什么又要判断呢？ 防止其它线程已经初始化完毕了，然后当前线程再次初始化..导致丢失数据。
                //条件成立，说明其它线程都没有进入过这个if块，当前线程就是具备初始化table权利了。
                if ((tab = table) == null || tab.length == 0) {

                    //sc大于0 创建table时 使用 sc为指定大小，否则使用 16 默认值.
                    int n = (sc > 0) ? sc : DEFAULT_CAPACITY;

                    @SuppressWarnings("unchecked")
                    Node<K,V>[] nt = (Node<K,V>[])new Node<?,?>[n];
                    //最终赋值给 map.table
                    table = tab = nt;
                    //n >>> 2  => 等于 1/4 n     n - (1/4)n = 3/4 n => 0.75 * n
                    //sc 0.75 n 表示下一次扩容时的触发条件。
                    sc = n - (n >>> 2);
                }
            } finally {
                //1.如果当前线程是第一次创建map.table的线程话，sc表示的是 下一次扩容的阈值
                //2.表示当前线程 并不是第一次创建map.table的线程，当前线程进入到else if 块 时，将
                //sizeCtl 设置为了-1 ，那么这时需要将其修改为 进入时的值。
                sizeCtl = sc;
            }
            break;
        }
    }
    return tab;
}
```
#7 addCount
```java
private final void addCount(long x, int check) {
    //as 表示 LongAdder.cells
    //b 表示LongAdder.base
    //s 表示当前map.table中元素的数量
    CounterCell[] as; long b, s;
    //条件一：true->表示cells已经初始化了，当前线程应该去使用hash寻址找到合适的cell 去累加数据
    //       false->表示当前线程应该将数据累加到 base
    //条件二：false->表示写base成功，数据累加到base中了，当前竞争不激烈，不需要创建cells
    //       true->表示写base失败，与其他线程在base上发生了竞争，当前线程应该去尝试创建cells。
    if ((as = counterCells) != null ||
        !U.compareAndSwapLong(this, BASECOUNT, b = baseCount, s = b + x)) {
        //有几种情况进入到if块中？
        //1.true->表示cells已经初始化了，当前线程应该去使用hash寻址找到合适的cell 去累加数据
        //2.true->表示写base失败，与其他线程在base上发生了竞争，当前线程应该去尝试创建cells。

        //a 表示当前线程hash寻址命中的cell
        CounterCell a;
        //v 表示当前线程写cell时的期望值
        long v;
        //m 表示当前cells数组的长度
        int m;
        //true -> 未竞争  false->发生竞争
        boolean uncontended = true;


        //条件一：as == null || (m = as.length - 1) < 0
        //true-> 表示当前线程是通过 写base竞争失败 然后进入的if块，就需要调用fullAddCount方法去扩容 或者 重试.. LongAdder.longAccumulate
        //条件二：a = as[ThreadLocalRandom.getProbe() & m]) == null   前置条件：cells已经初始化了
        //true->表示当前线程命中的cell表格是个空，需要当前线程进入fullAddCount方法去初始化 cell，放入当前位置.
        //条件三：!(uncontended = U.compareAndSwapLong(a, CELLVALUE, v = a.value, v + x)
        //      false->取反得到false，表示当前线程使用cas方式更新当前命中的cell成功
        //      true->取反得到true,表示当前线程使用cas方式更新当前命中的cell失败，需要进入fullAddCount进行重试 或者 扩容 cells。
        if (as == null || (m = as.length - 1) < 0 ||
            (a = as[ThreadLocalRandom.getProbe() & m]) == null ||
            !(uncontended = U.compareAndSwapLong(a, CELLVALUE, v = a.value, v + x))
           ) {
            fullAddCount(x, uncontended);
            //考虑到fullAddCount里面的事情比较累，就让当前线程 不参与到 扩容相关的逻辑了，直接返回到调用点。
            return;
        }

        if (check <= 1)
            return;

        //获取当前散列表元素个数，这是一个期望值
        s = sumCount();
    }

    //表示一定是一个put操作调用的addCount
    if (check >= 0) {
        //tab 表示map.table
        //nt 表示map.nextTable
        //n 表示map.table数组的长度
        //sc 表示sizeCtl的临时值
        Node<K,V>[] tab, nt; int n, sc;


        /**
             * sizeCtl < 0
             * 1. -1 表示当前table正在初始化（有线程在创建table数组），当前线程需要自旋等待..
             * 2.表示当前table数组正在进行扩容 ,高16位表示：扩容的标识戳   低16位表示：（1 + nThread） 当前参与并发扩容的线程数量
             *
             * sizeCtl = 0，表示创建table数组时 使用DEFAULT_CAPACITY为大小
             *
             * sizeCtl > 0
             *
             * 1. 如果table未初始化，表示初始化大小
             * 2. 如果table已经初始化，表示下次扩容时的 触发条件（阈值）
             */

        //自旋
        //条件一：s >= (long)(sc = sizeCtl)
        //       true-> 1.当前sizeCtl为一个负数 表示正在扩容中..
        //              2.当前sizeCtl是一个正数，表示扩容阈值
        //       false-> 表示当前table尚未达到扩容条件
        //条件二：(tab = table) != null
        //       恒成立 true
        //条件三：(n = tab.length) < MAXIMUM_CAPACITY
        //       true->当前table长度小于最大值限制，则可以进行扩容。
        while (s >= (long)(sc = sizeCtl) && (tab = table) != null &&
               (n = tab.length) < MAXIMUM_CAPACITY) {

            //扩容批次唯一标识戳
            //16 -> 32 扩容 标识为：1000 0000 0001 1011
            int rs = resizeStamp(n);

            //条件成立：表示当前table正在扩容
            //         当前线程理论上应该协助table完成扩容
            if (sc < 0) {
                //条件一：(sc >>> RESIZE_STAMP_SHIFT) != rs
                //      true->说明当前线程获取到的扩容唯一标识戳 非 本批次扩容
                //      false->说明当前线程获取到的扩容唯一标识戳 是 本批次扩容
                //条件二： JDK1.8 中有bug jira已经提出来了 其实想表达的是 =  sc == (rs << 16 ) + 1
                //        true-> 表示扩容完毕，当前线程不需要再参与进来了
                //        false->扩容还在进行中，当前线程可以参与
                //条件三：JDK1.8 中有bug jira已经提出来了 其实想表达的是 = sc == (rs<<16) + MAX_RESIZERS
                //        true-> 表示当前参与并发扩容的线程达到了最大值 65535 - 1
                //        false->表示当前线程可以参与进来
                //条件四：(nt = nextTable) == null
                //        true->表示本次扩容结束
                //        false->扩容正在进行中
                if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 ||
                    sc == rs + MAX_RESIZERS || (nt = nextTable) == null ||
                    transferIndex <= 0)
                    break;

                //前置条件：当前table正在执行扩容中.. 当前线程有机会参与进扩容。
                //条件成立：说明当前线程成功参与到扩容任务中，并且将sc低16位值加1，表示多了一个线程参与工作
                //条件失败：1.当前有很多线程都在此处尝试修改sizeCtl，有其它一个线程修改成功了，导致你的sc期望值与内存中的值不一致 修改失败
                //        2.transfer 任务内部的线程也修改了sizeCtl。
                if (U.compareAndSwapInt(this, SIZECTL, sc, sc + 1))
                    //协助扩容线程，持有nextTable参数
                    transfer(tab, nt);
            }
            //1000 0000 0001 1011 0000 0000 0000 0000 +2 => 1000 0000 0001 1011 0000 0000 0000 0010
            //条件成立，说明当前线程是触发扩容的第一个线程，在transfer方法需要做一些扩容准备工作
            else if (U.compareAndSwapInt(this, SIZECTL, sc,
                                         (rs << RESIZE_STAMP_SHIFT) + 2))
                //触发扩容条件的线程 不持有nextTable
                transfer(tab, null);
            s = sumCount();
        }
    }
}
```
#8. transfer
ConcurrentHashMap 支持并发扩容，实现方式是，把 Node 数组进行拆分，让每个线程处理自己的区域，假设 table 数组总长度是 64，默认情况下，那么每个线程可以分到 16 个 bucket。然后每个线程处理的范围，按照倒序来做迁移。

通过 for 自循环处理每个槽位中的链表元素，默认 advace 为真，通过 CAS 设置 transferIndex属性值，并初始化 i 和 bound 值，i 指当前处理的槽位序号，bound 指需要处理的槽位边界，先处理槽位 31 的节点； （bound,i） =(16,31) 从 31 的位置往前推动。

每存在一个线程执行完扩容操作，就通过 cas 执行 sc-1。

接着判断(sc-2) !=resizeStamp(n) << RESIZE_STAMP_SHIFT ; 如果相等，表示当前为整个扩容操作的 最后一个线程，那么意味着整个扩容操作就结束了；如果不相等，说明还得继续。

这么做的目的，一方面是防止不同扩容之间出现相同的 sizeCtl，另外一方面，还可以避免sizeCtl 的 ABA 问题导致的扩容重叠的情况。

**扩容图解**
![img.png](./img/concurrenthashmap扩容图解.png)
判断是否需要扩容，也就是当更新后的键值对总数 baseCount >= 阈值 sizeCtl 时，进行rehash，这里面会有两个逻辑。

1. 如果当前正在处于扩容阶段，则当前线程会加入并且协助扩容。
2. 如果当前没有在扩容，则直接触发扩容操作。

扩容操作的核心在于数据的转移，在单线程环境下数据的转移很简单，无非就是把旧数组中的数据迁移到新的数组。但是这在多线程环境下，在扩容的时候其他线程也可能正在添加元素，这时又触发了扩容怎么办？可能大家想到的第一个解决方案是加互斥锁，把转移过程锁住，虽然是可行的解决方案，但是会带来较大的性能开销。因为互斥锁会导致所有访问临界区的线程陷入到阻塞状态，持有锁的线程耗时越长，其他竞争线程就会一直被阻塞，导致吞吐量较低。而且还可能导致死锁。

而 ConcurrentHashMap 并没有直接加锁，而是采用 CAS 实现无锁的并发同步策略，最精华的部分是它可以利用多线程来进行协同扩容。

它把 Node 数组当作多个线程之间共享的任务队列，然后通过维护一个指针来划分每个线程锁负责的区间，每个线程通过区间逆向遍历来实现扩容，一个已经迁移完的bucket会被替换为一个ForwardingNode节点，标记当前bucket已经被其他线程迁移完了。接下来分析一下它的源码实现。

fwd:这个类是个标识类，用于指向新表用的，其他线程遇到这个类会主动跳过这个类，因为这个类要么就是扩容迁移正在进行，要么就是已经完成扩容迁移，也就是这个类要保证线程安全，再进行操作。

advance:这个变量是用于提示代码是否进行推进处理，也就是当前桶处理完，处理下一个桶的标识。

finishing:这个变量用于提示扩容是否结束用的。
```java
private final void transfer(Node<K,V>[] tab, Node<K,V>[] nextTab) {
    //n 表示扩容之前table数组的长度
    //stride 表示分配给线程任务的步长
    int n = tab.length, stride;
    //  stride 固定为 16
    if ((stride = (NCPU > 1) ? (n >>> 3) / NCPU : n) < MIN_TRANSFER_STRIDE)
        stride = MIN_TRANSFER_STRIDE; // subdivide range


    //条件成立：表示当前线程为触发本次扩容的线程，需要做一些扩容准备工作
    //条件不成立：表示当前线程是协助扩容的线程..
    if (nextTab == null) {            // initiating
        try {
            //创建了一个比扩容之前大一倍的table
            @SuppressWarnings("unchecked")
            Node<K,V>[] nt = (Node<K,V>[])new Node<?,?>[n << 1];
            nextTab = nt;
        } catch (Throwable ex) {      // try to cope with OOME
            sizeCtl = Integer.MAX_VALUE;
            return;
        }
        //赋值给对象属性 nextTable ，方便协助扩容线程 拿到新表
        nextTable = nextTab;
        //记录迁移数据整体位置的一个标记。index计数是从1开始计算的。
        transferIndex = n;
    }

    //表示新数组的长度
    int nextn = nextTab.length;
    //fwd 节点，当某个桶位数据处理完毕后，将此桶位设置为fwd节点，其它写线程 或读线程看到后，会有不同逻辑。
    ForwardingNode<K,V> fwd = new ForwardingNode<K,V>(nextTab);
    //推进标记
    boolean advance = true;
    //完成标记
    boolean finishing = false; // to ensure sweep before committing nextTab

    //i 表示分配给当前线程任务，执行到的桶位
    //bound 表示分配给当前线程任务的下界限制
    int i = 0, bound = 0;
    //自旋
    for (;;) {
        //f 桶位的头结点
        //fh 头结点的hash
        Node<K,V> f; int fh;


        /**
             * 1.给当前线程分配任务区间
             * 2.维护当前线程任务进度（i 表示当前处理的桶位）
             * 3.维护map对象全局范围内的进度
             */
        while (advance) {
            //分配任务的开始下标
            //分配任务的结束下标
            int nextIndex, nextBound;

            //CASE1:
            //条件一：--i >= bound
            //成立：表示当前线程的任务尚未完成，还有相应的区间的桶位要处理，--i 就让当前线程处理下一个 桶位.
            //不成立：表示当前线程任务已完成 或 者未分配
            if (--i >= bound || finishing)
                advance = false;
            //CASE2:
            //前置条件：当前线程任务已完成 或 者未分配
            //条件成立：表示对象全局范围内的桶位都分配完毕了，没有区间可分配了，设置当前线程的i变量为-1 跳出循环后，执行退出迁移任务相关的程序
            //条件不成立：表示对象全局范围内的桶位尚未分配完毕，还有区间可分配
            else if ((nextIndex = transferIndex) <= 0) {
                i = -1;
                advance = false;
            }
            //CASE3:
            //前置条件：1、当前线程需要分配任务区间  2.全局范围内还有桶位尚未迁移
            //条件成立：说明给当前线程分配任务成功
            //条件失败：说明分配给当前线程失败，应该是和其它线程发生了竞争吧
            else if (U.compareAndSwapInt
                     (this, TRANSFERINDEX, nextIndex,
                      nextBound = (nextIndex > stride ?
                                   nextIndex - stride : 0))) {

                bound = nextBound;
                i = nextIndex - 1;
                advance = false;
            }
        }

        //CASE1：
        //条件一：i < 0
        //成立：表示当前线程未分配到任务
        if (i < 0 || i >= n || i + n >= nextn) {
            //保存sizeCtl 的变量
            int sc;
            if (finishing) {
                nextTable = null;
                table = nextTab;
                sizeCtl = (n << 1) - (n >>> 1);
                return;
            }

            //条件成立：说明设置sizeCtl 低16位  -1 成功，当前线程可以正常退出
            if (U.compareAndSwapInt(this, SIZECTL, sc = sizeCtl, sc - 1)) {
                //1000 0000 0001 1011 0000 0000 0000 0000
                //条件成立：说明当前线程不是最后一个退出transfer任务的线程
                if ((sc - 2) != resizeStamp(n) << RESIZE_STAMP_SHIFT)
                    //正常退出
                    return;

                finishing = advance = true;
                i = n; // recheck before commit
            }
        }
        //前置条件：【CASE2~CASE4】 当前线程任务尚未处理完，正在进行中

        //CASE2:
        //条件成立：说明当前桶位未存放数据，只需要将此处设置为fwd节点即可。
        else if ((f = tabAt(tab, i)) == null)
            advance = casTabAt(tab, i, null, fwd);
        //CASE3:
        //条件成立：说明当前桶位已经迁移过了，当前线程不用再处理了，直接再次更新当前线程任务索引，再次处理下一个桶位 或者 其它操作
        else if ((fh = f.hash) == MOVED)
            advance = true; // already processed
        //CASE4:
        //前置条件：当前桶位有数据，而且node节点 不是 fwd节点，说明这些数据需要迁移。
        else {
            //sync 加锁当前桶位的头结点
            synchronized (f) {
                //防止在你加锁头对象之前，当前桶位的头对象被其它写线程修改过，导致你目前加锁对象错误...
                if (tabAt(tab, i) == f) {
                    //ln 表示低位链表引用
                    //hn 表示高位链表引用
                    Node<K,V> ln, hn;

                    //条件成立：表示当前桶位是链表桶位
                    if (fh >= 0) {


                        //lastRun
                        //可以获取出 当前链表 末尾连续高位不变的 node
                        int runBit = fh & n;
                        Node<K,V> lastRun = f;
                        for (Node<K,V> p = f.next; p != null; p = p.next) {
                            int b = p.hash & n;
                            if (b != runBit) {
                                runBit = b;
                                lastRun = p;
                            }
                        }

                        //条件成立：说明lastRun引用的链表为 低位链表，那么就让 ln 指向 低位链表
                        if (runBit == 0) {
                            ln = lastRun;
                            hn = null;
                        }
                        //否则，说明lastRun引用的链表为 高位链表，就让 hn 指向 高位链表
                        else {
                            hn = lastRun;
                            ln = null;
                        }



                        for (Node<K,V> p = f; p != lastRun; p = p.next) {
                            int ph = p.hash; K pk = p.key; V pv = p.val;
                            if ((ph & n) == 0)
                                ln = new Node<K,V>(ph, pk, pv, ln);
                            else
                                hn = new Node<K,V>(ph, pk, pv, hn);
                        }



                        setTabAt(nextTab, i, ln);
                        setTabAt(nextTab, i + n, hn);
                        setTabAt(tab, i, fwd);
                        advance = true;
                    }
                    //条件成立：表示当前桶位是 红黑树 代理结点TreeBin
                    else if (f instanceof TreeBin) {
                        //转换头结点为 treeBin引用 t
                        TreeBin<K,V> t = (TreeBin<K,V>)f;

                        //低位双向链表 lo 指向低位链表的头  loTail 指向低位链表的尾巴
                        TreeNode<K,V> lo = null, loTail = null;
                        //高位双向链表 lo 指向高位链表的头  loTail 指向高位链表的尾巴
                        TreeNode<K,V> hi = null, hiTail = null;


                        //lc 表示低位链表元素数量
                        //hc 表示高位链表元素数量
                        int lc = 0, hc = 0;

                        //迭代TreeBin中的双向链表，从头结点 至 尾节点
                        for (Node<K,V> e = t.first; e != null; e = e.next) {
                            // h 表示循环处理当前元素的 hash
                            int h = e.hash;
                            //使用当前节点 构建出来的 新的 TreeNode
                            TreeNode<K,V> p = new TreeNode<K,V>
                                (h, e.key, e.val, null, null);

                            //条件成立：表示当前循环节点 属于低位链 节点
                            if ((h & n) == 0) {
                                //条件成立：说明当前低位链表 还没有数据
                                if ((p.prev = loTail) == null)
                                    lo = p;
                                //说明 低位链表已经有数据了，此时当前元素 追加到 低位链表的末尾就行了
                                else
                                    loTail.next = p;
                                //将低位链表尾指针指向 p 节点
                                loTail = p;
                                ++lc;
                            }
                            //当前节点 属于 高位链 节点
                            else {
                                if ((p.prev = hiTail) == null)
                                    hi = p;
                                else
                                    hiTail.next = p;
                                hiTail = p;
                                ++hc;
                            }
                        }



                        ln = (lc <= UNTREEIFY_THRESHOLD) ? untreeify(lo) :
                        (hc != 0) ? new TreeBin<K,V>(lo) : t;
                        hn = (hc <= UNTREEIFY_THRESHOLD) ? untreeify(hi) :
                        (lc != 0) ? new TreeBin<K,V>(hi) : t;
                        setTabAt(nextTab, i, ln);
                        setTabAt(nextTab, i + n, hn);
                        setTabAt(tab, i, fwd);
                        advance = true;
                    }
                }
            }
        }
    }
}
```
链表迁移原理

1）高低位原理分析

ConcurrentHashMap 在做链表迁移时，会用高低位来实现，这里有两个问题要分析一下

1，如何实现高低位链表的区分

假如有这样一个队列
![img_1.png](./img/concurrenthashmap迁移高低位原理1.png)
第 14 个槽位插入新节点之后，链表元素个数已经达到了 8，且数组长度为 16，优先通过扩容来缓解链表过长的问题

假如当前线程正在处理槽位为 14 的节点，它是一个链表结构，在代码中，首先定义两个变量节点 ln 和 hn，实际就是 lowNode 和 HighNode，分别保存 hash 值的第 x 位为 0 和不等于0 的节点

通过 fn&n 可以把这个链表中的元素分为两类，A 类是 hash 值的第 X 位为 0，B 类是 hash 值的第 x 位为不等于 0（至于为什么要这么区分，稍后分析），并且通过 lastRun 记录最后要处理的节点。最终要达到的目的是，A 类的链表保持位置不动，B 类的链表为 14+16(扩容增加的长度)=30

把 14 槽位的链表单独伶出来，用蓝色表示 fn&n=0 的节点，假如链表的分类是这样

![111](./img/ffb2efa924944e02b25e97a2b90bf6f5.png)
```java
for (Node<K,V> p = f.next; p != null; p = p.next) {
	int b = p.hash & n;
	if (b != runBit) {
        runBit = b;
        lastRun = p;
	}
}
```
通过上面这段代码遍历，会记录 runBit 以及 lastRun，按照上面这个结构，那么 runBit 应该是蓝色节点，lastRun 应该是第 6 个节点接着，再通过这段代码进行遍历，生成 ln 链以及 hn 链

```java
for (Node<K,V> p = f; p != lastRun; p = p.next) {
    int ph = p.hash; K pk = p.key; V pv = p.val;
    if ((ph & n) == 0)
    	ln = new Node<K,V>(ph, pk, pv, ln);
    else
    	hn = new Node<K,V>(ph, pk, pv, hn);
}
```
![111](./img/3914c7b94d2843b985ea10e5c23a04b0.png)
接着，通过 CAS 操作，把 hn 链放在 i+n 也就是 14+16 的位置，ln 链保持原来的位置不动。并且设置当前节点为 fwd，表示已经被当前线程迁移完了。
```java
setTabAt(nextTab, i, ln);
setTabAt(nextTab, i + n, hn);
setTabAt(tab, i, fwd);
```
迁移完成以后的数据分布如下

![111](./img/e7e01e24e3e844c7b31c4d73da2fffed.png)
2）为什么要做高低位的划分

要想了解这么设计的目的，我们需要从 ConcurrentHashMap 的根据下标获取对象的算法来看，在 putVal 方法中 1018 行：

```(f = tabAt(tab, i = (n - 1) & hash)) == null```

通过(n-1) & hash 来获得在 table 中的数组下标来获取节点数据，【&运算是二进制运算符，1& 1=1，其他都为 0】。

![111](./img/db389ed8b874494ca1f5a8723e8a6973.png)
#9.helpTransfer
如果对应的节点存在，判断这个节点的 hash 是不是等于 MOVED(-1)，说明当前节点是ForwardingNode 节点，意味着有其他线程正在进行扩容，那么当前现在直接帮助它进行扩容，因此调用 helpTransfer方法。

```java
final Node<K,V>[] helpTransfer(Node<K,V>[] tab, Node<K,V> f) {
    //nextTab 引用的是 fwd.nextTable == map.nextTable 理论上是这样。
    //sc 保存map.sizeCtl
    Node<K,V>[] nextTab; int sc;

    //条件一：tab != null 恒成立 true
    //条件二：(f instanceof ForwardingNode) 恒成立 true
    //条件三：((ForwardingNode<K,V>)f).nextTable) != null 恒成立 true
    if (tab != null && (f instanceof ForwardingNode) &&
        (nextTab = ((ForwardingNode<K,V>)f).nextTable) != null) {

        //拿当前标的长度 获取 扩容标识戳   假设 16 -> 32 扩容：1000 0000 0001 1011
        int rs = resizeStamp(tab.length);

        //条件一：nextTab == nextTable
        //成立：表示当前扩容正在进行中
        //不成立：1.nextTable被设置为Null 了，扩容完毕后，会被设为Null
        //       2.再次出发扩容了...咱们拿到的nextTab 也已经过期了...
        //条件二：table == tab
        //成立：说明 扩容正在进行中，还未完成
        //不成立：说明扩容已经结束了，扩容结束之后，最后退出的线程 会设置 nextTable 为 table

        //条件三：(sc = sizeCtl) < 0
        //成立：说明扩容正在进行中
        //不成立：说明sizeCtl当前是一个大于0的数，此时代表下次扩容的阈值，当前扩容已经结束。
        while (nextTab == nextTable && table == tab &&
               (sc = sizeCtl) < 0) {


            //条件一：(sc >>> RESIZE_STAMP_SHIFT) != rs
            //      true->说明当前线程获取到的扩容唯一标识戳 非 本批次扩容
            //      false->说明当前线程获取到的扩容唯一标识戳 是 本批次扩容
            //条件二： JDK1.8 中有bug jira已经提出来了 其实想表达的是 =  sc == (rs << 16 ) + 1
            //        true-> 表示扩容完毕，当前线程不需要再参与进来了
            //        false->扩容还在进行中，当前线程可以参与
            //条件三：JDK1.8 中有bug jira已经提出来了 其实想表达的是 = sc == (rs<<16) + MAX_RESIZERS
            //        true-> 表示当前参与并发扩容的线程达到了最大值 65535 - 1
            //        false->表示当前线程可以参与进来
            //条件四：transferIndex <= 0
            //      true->说明map对象全局范围内的任务已经分配完了，当前线程进去也没活干..
            //      false->还有任务可以分配。
            if ((sc >>> RESIZE_STAMP_SHIFT) != rs || sc == rs + 1 ||
                sc == rs + MAX_RESIZERS || transferIndex <= 0)
                break;


            if (U.compareAndSwapInt(this, SIZECTL, sc, sc + 1)) {
                transfer(tab, nextTab);
                break;
            }
        }
        return nextTab;
    }
    return table;
}
```
#10.get
```java
public V get(Object key) {
    //tab 引用map.table
    //e 当前元素
    //p 目标节点
    //n table数组长度
    //eh 当前元素hash
    //ek 当前元素key
    Node<K,V>[] tab; Node<K,V> e, p; int n, eh; K ek;
    //扰动运算后得到 更散列的hash值
    int h = spread(key.hashCode());

    //条件一：(tab = table) != null
    //true->表示已经put过数据，并且map内部的table也已经初始化完毕
    //false->表示创建完map后，并没有put过数据，map内部的table是延迟初始化的，只有第一次写数据时会触发创建逻辑。
    //条件二：(n = tab.length) > 0 true->表示table已经初始化
    //条件三：(e = tabAt(tab, (n - 1) & h)) != null
    //true->当前key寻址的桶位 有值
    //false->当前key寻址的桶位中是null，是null直接返回null
    if ((tab = table) != null && (n = tab.length) > 0 &&
        (e = tabAt(tab, (n - 1) & h)) != null) {
        //前置条件：当前桶位有数据

        //对比头结点hash与查询key的hash是否一致
        //条件成立：说明头结点与查询Key的hash值 完全一致
        if ((eh = e.hash) == h) {
            //完全比对 查询key 和 头结点的key
            //条件成立：说明头结点就是查询数据
            if ((ek = e.key) == key || (ek != null && key.equals(ek)))
                return e.val;
        }

        //条件成立：
        //1.-1  fwd 说明当前table正在扩容，且当前查询的这个桶位的数据 已经被迁移走了
        //2.-2  TreeBin节点，需要使用TreeBin 提供的find 方法查询。
        else if (eh < 0)
            return (p = e.find(h, key)) != null ? p.val : null;




        //当前桶位已经形成链表的这种情况
        while ((e = e.next) != null) {
            if (e.hash == h &&
                ((ek = e.key) == key || (ek != null && key.equals(ek))))
                return e.val;
        }

    }
    return null;
}
```
#11.remove
```java
public V remove(Object key) {
    return replaceNode(key, null, null);
}
```
#12.replaceNode
```java
final V replaceNode(Object key, V value, Object cv) {
    //计算key经过扰动运算后的hash
    int hash = spread(key.hashCode());
    //自旋
    for (Node<K,V>[] tab = table;;) {
        //f表示桶位头结点
        //n表示当前table数组长度
        //i表示hash命中桶位下标
        //fh表示桶位头结点 hash
        Node<K,V> f; int n, i, fh;

        //CASE1：
        //条件一：tab == null  true->表示当前map.table尚未初始化..  false->已经初始化
        //条件二：(n = tab.length) == 0  true->表示当前map.table尚未初始化..  false->已经初始化
        //条件三：(f = tabAt(tab, i = (n - 1) & hash)) == null true -> 表示命中桶位中为null，直接break， 会返回
        if (tab == null || (n = tab.length) == 0 ||
            (f = tabAt(tab, i = (n - 1) & hash)) == null)
            break;

        //CASE2：
        //前置条件CASE2 ~ CASE3：当前桶位不是null
        //条件成立：说明当前table正在扩容中，当前是个写操作，所以当前线程需要协助table完成扩容。
        else if ((fh = f.hash) == MOVED)
            tab = helpTransfer(tab, f);

        //CASE3:
        //前置条件CASE2 ~ CASE3：当前桶位不是null
        //当前桶位 可能是 "链表" 也可能 是  "红黑树" TreeBin
        else {
            //保留替换之前的数据引用
            V oldVal = null;
            //校验标记
            boolean validated = false;
            //加锁当前桶位 头结点，加锁成功之后会进入 代码块。
            synchronized (f) {
                //判断sync加锁是否为当前桶位 头节点，防止其它线程，在当前线程加锁成功之前，修改过 桶位 的头结点。
                //条件成立：当前桶位头结点 仍然为f，其它线程没修改过。
                if (tabAt(tab, i) == f) {
                    //条件成立：说明桶位 为 链表 或者 单个 node
                    if (fh >= 0) {
                        validated = true;

                        //e 表示当前循环处理元素
                        //pred 表示当前循环节点的上一个节点
                        Node<K,V> e = f, pred = null;
                        for (;;) {
                            //当前节点key
                            K ek;
                            //条件一：e.hash == hash true->说明当前节点的hash与查找节点hash一致
                            //条件二：((ek = e.key) == key || (ek != null && key.equals(ek)))
                            //if 条件成立，说明key 与查询的key完全一致。
                            if (e.hash == hash &&
                                ((ek = e.key) == key ||
                                 (ek != null && key.equals(ek)))) {
                                //当前节点的value
                                V ev = e.val;

                                //条件一：cv == null true->替换的值为null 那么就是一个删除操作
                                //条件二：cv == ev || (ev != null && cv.equals(ev))  那么是一个替换操作
                                if (cv == null || cv == ev ||
                                    (ev != null && cv.equals(ev))) {
                                    //删除 或者 替换

                                    //将当前节点的值 赋值给 oldVal 后续返回会用到
                                    oldVal = ev;

                                    //条件成立：说明当前是一个替换操作
                                    if (value != null)
                                        //直接替换
                                        e.val = value;
                                    //条件成立：说明当前节点非头结点
                                    else if (pred != null)
                                        //当前节点的上一个节点，指向当前节点的下一个节点。
                                        pred.next = e.next;

                                    else
                                        //说明当前节点即为 头结点，只需要将 桶位设置为头结点的下一个节点。
                                        setTabAt(tab, i, e.next);
                                }
                                break;
                            }
                            pred = e;
                            if ((e = e.next) == null)
                                break;
                        }
                    }

                    //条件成立：TreeBin节点。
                    else if (f instanceof TreeBin) {
                        validated = true;

                        //转换为实际类型 TreeBin t
                        TreeBin<K,V> t = (TreeBin<K,V>)f;
                        //r 表示 红黑树 根节点
                        //p 表示 红黑树中查找到对应key 一致的node
                        TreeNode<K,V> r, p;

                        //条件一：(r = t.root) != null 理论上是成立
                        //条件二：TreeNode.findTreeNode 以当前节点为入口，向下查找key（包括本身节点）
                        //      true->说明查找到相应key 对应的node节点。会赋值给p
                        if ((r = t.root) != null &&
                            (p = r.findTreeNode(hash, key, null)) != null) {
                            //保存p.val 到pv
                            V pv = p.val;

                            //条件一：cv == null  成立：不必对value，就做替换或者删除操作
                            //条件二：cv == pv ||(pv != null && cv.equals(pv)) 成立：说明“对比值”与当前p节点的值 一致
                            if (cv == null || cv == pv ||
                                (pv != null && cv.equals(pv))) {
                                //替换或者删除操作


                                oldVal = pv;

                                //条件成立：替换操作
                                if (value != null)
                                    p.val = value;


                                //删除操作
                                else if (t.removeTreeNode(p))
                                    //这里没做判断，直接搞了...很疑惑
                                    setTabAt(tab, i, untreeify(t.first));
                            }
                        }
                    }
                }
            }
            //当其他线程修改过桶位 头结点时，当前线程 sync 头结点 锁错对象时，validated 为false，会进入下次for 自旋
            if (validated) {

                if (oldVal != null) {
                    //替换的值 为null，说明当前是一次删除操作，oldVal ！=null 成立，说明删除成功，更新当前元素个数计数器。
                    if (value == null)
                        addCount(-1L, -1);
                    return oldVal;
                }
                break;
            }
        }
    }
    return null;
}
```
#13.TreeBin
##13.1 属性
```java
//红黑树 根节点 
TreeNode<K,V> root;
//链表的头节点
volatile TreeNode<K,V> first;
//等待者线程（当前lockState是读锁状态）
volatile Thread waiter;
/**
         * 1.写锁状态 写是独占状态，以散列表来看，真正进入到TreeBin中的写线程 同一时刻 只有一个线程。 1
         * 2.读锁状态 读锁是共享，同一时刻可以有多个线程 同时进入到 TreeBin对象中获取数据。 每一个线程 都会给 lockStat + 4
         * 3.等待者状态（写线程在等待），当TreeBin中有读线程目前正在读取数据时，写线程无法修改数据，那么就将lockState的最低2位 设置为 0b 10
         */
volatile int lockState;

// values for lockState
static final int WRITER = 1; // set while holding write lock
static final int WAITER = 2; // set when waiting for write lock
static final int READER = 4; // increment value for setting read lock
```
##13.2 构造器
```java
TreeBin(TreeNode<K,V> b) {
    //设置节点hash为-2 表示此节点是TreeBin节点
    super(TREEBIN, null, null, null);
    //使用first 引用 treeNode链表
    this.first = b;
    //r 红黑树的根节点引用
    TreeNode<K,V> r = null;

    //x表示遍历的当前节点
    for (TreeNode<K,V> x = b, next; x != null; x = next) {
        next = (TreeNode<K,V>)x.next;
        //强制设置当前插入节点的左右子树为null
        x.left = x.right = null;
        //条件成立：说明当前红黑树 是一个空树，那么设置插入元素 为根节点
        if (r == null) {
            //根节点的父节点 一定为 null
            x.parent = null;
            //颜色改为黑色
            x.red = false;
            //让r引用x所指向的对象。
            r = x;
        }

        else {
            //非第一次循环，都会来带else分支，此时红黑树已经有数据了

            //k 表示 插入节点的key
            K k = x.key;
            //h 表示 插入节点的hash
            int h = x.hash;
            //kc 表示 插入节点key的class类型
            Class<?> kc = null;
            //p 表示 为查找插入节点的父节点的一个临时节点
            TreeNode<K,V> p = r;

            for (;;) {
                //dir (-1, 1)
                //-1 表示插入节点的hash值大于 当前p节点的hash
                //1 表示插入节点的hash值 小于 当前p节点的hash
                //ph p表示 为查找插入节点的父节点的一个临时节点的hash
                int dir, ph;
                //临时节点 key
                K pk = p.key;

                //插入节点的hash值 小于 当前节点
                if ((ph = p.hash) > h)
                    //插入节点可能需要插入到当前节点的左子节点 或者 继续在左子树上查找
                    dir = -1;
                //插入节点的hash值 大于 当前节点
                else if (ph < h)
                    //插入节点可能需要插入到当前节点的右子节点 或者 继续在右子树上查找
                    dir = 1;

                //如果执行到 CASE3，说明当前插入节点的hash 与 当前节点的hash一致，会在case3 做出最终排序。最终
                //拿到的dir 一定不是0，（-1， 1）
                else if ((kc == null &&
                          (kc = comparableClassFor(k)) == null) ||
                         (dir = compareComparables(kc, k, pk)) == 0)
                    dir = tieBreakOrder(k, pk);

                //xp 想要表示的是 插入节点的 父节点
                TreeNode<K,V> xp = p;
                //条件成立：说明当前p节点 即为插入节点的父节点
                //条件不成立：说明p节点 底下还有层次，需要将p指向 p的左子节点 或者 右子节点，表示继续向下搜索。
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    //设置插入节点的父节点 为 当前节点
                    x.parent = xp;
                    //小于P节点，需要插入到P节点的左子节点
                    if (dir <= 0)
                        xp.left = x;

                    //大于P节点，需要插入到P节点的右子节点
                    else
                        xp.right = x;

                    //插入节点后，红黑树性质 可能会被破坏，所以需要调用 平衡方法
                    r = balanceInsertion(r, x);
                    break;
                }
            }
        }
    }
    //将r 赋值给 TreeBin对象的 root引用。
    this.root = r;
    assert checkInvariants(root);
}
```
##13.3 putTreeVal
```java
final TreeNode<K,V> putTreeVal(int h, K k, V v) {
    Class<?> kc = null;
    boolean searched = false;
    for (TreeNode<K,V> p = root;;) {
        int dir, ph; K pk;
        if (p == null) {
            first = root = new TreeNode<K,V>(h, k, v, null, null);
            break;
        }
        else if ((ph = p.hash) > h)
            dir = -1;
        else if (ph < h)
            dir = 1;
        else if ((pk = p.key) == k || (pk != null && k.equals(pk)))
            return p;
        else if ((kc == null &&
                  (kc = comparableClassFor(k)) == null) ||
                 (dir = compareComparables(kc, k, pk)) == 0) {
            if (!searched) {
                TreeNode<K,V> q, ch;
                searched = true;
                if (((ch = p.left) != null &&
                     (q = ch.findTreeNode(h, k, kc)) != null) ||
                    ((ch = p.right) != null &&
                     (q = ch.findTreeNode(h, k, kc)) != null))
                    return q;
            }
            dir = tieBreakOrder(k, pk);
        }


        TreeNode<K,V> xp = p;
        if ((p = (dir <= 0) ? p.left : p.right) == null) {
            //当前循环节点xp 即为 x 节点的爸爸

            //x 表示插入节点
            //f 老的头结点
            TreeNode<K,V> x, f = first;
            first = x = new TreeNode<K,V>(h, k, v, f, xp);

            //条件成立：说明链表有数据
            if (f != null)
                //设置老的头结点的前置引用为 当前的头结点。
                f.prev = x;


            if (dir <= 0)
                xp.left = x;
            else
                xp.right = x;


            if (!xp.red)
                x.red = true;
            else {
                //表示 当前新插入节点后，新插入节点 与 父节点 形成 “红红相连”
                lockRoot();
                try {
                    //平衡红黑树，使其再次符合规范。
                    root = balanceInsertion(root, x);
                } finally {
                    unlockRoot();
                }
            }
            break;
        }
    }
    assert checkInvariants(root);
    return null;
}
```
##13.4 find
```java
final Node<K,V> find(int h, Object k) {
    if (k != null) {

        //e 表示循环迭代的当前节点   迭代的是first引用的链表
        for (Node<K,V> e = first; e != null; ) {
            //s 保存的是lock临时状态
            //ek 链表当前节点 的key
            int s; K ek;


            //(WAITER|WRITER) => 0010 | 0001 => 0011
            //lockState & 0011 != 0 条件成立：说明当前TreeBin 有等待者线程 或者 目前有写操作线程正在加锁
            if (((s = lockState) & (WAITER|WRITER)) != 0) {
                if (e.hash == h &&
                    ((ek = e.key) == k || (ek != null && k.equals(ek))))
                    return e;
                e = e.next;
            }

            //前置条件：当前TreeBin中 等待者线程 或者 写线程 都没有
            //条件成立：说明添加读锁成功
            else if (U.compareAndSwapInt(this, LOCKSTATE, s,
                                         s + READER)) {
                TreeNode<K,V> r, p;
                try {
                    //查询操作
                    p = ((r = root) == null ? null :
                         r.findTreeNode(h, k, null));
                } finally {
                    //w 表示等待者线程
                    Thread w;
                    //U.getAndAddInt(this, LOCKSTATE, -READER) == (READER|WAITER)
                    //1.当前线程查询红黑树结束，释放当前线程的读锁 就是让 lockstate 值 - 4
                    //(READER|WAITER) = 0110 => 表示当前只有一个线程在读，且“有一个线程在等待”
                    //当前读线程为 TreeBin中的最后一个读线程。

                    //2.(w = waiter) != null 说明有一个写线程在等待读操作全部结束。
                    if (U.getAndAddInt(this, LOCKSTATE, -READER) ==
                        (READER|WAITER) && (w = waiter) != null)
                        //使用unpark 让 写线程 恢复运行状态。
                        LockSupport.unpark(w);
                }
                return p;
            }
        }
    }
    return null;
}
```
#总结
在java8中，ConcurrentHashMap使用数组+链表+红黑树的组合方式，利用cas和synchronized保证并发写的安全。

引入红黑树的原因：链表查询的时间复杂度为On，但是红黑树的查询时间复杂度为O(log(n)),所以在节点比较多的情况下，使用红黑树可以大大提升性能。

链式桶是一个由node节点组成的链表。树状桶是一颗由TreeNode节点组成的红黑树。输的根节点为TreeBin类型。

当链表长度大于8整个hash表长度大于64的时候，就会转化为TreeBin。TreeBin作为根节点，其实就是红黑树对象。在ConcurrentHashMap的table数组中，存放的就是TreeBin对象，而不是TreeNoe对象。

数组table是懒加载的，只有第一次添加元素的时候才会初始化，所以initTable()存在线程安全问题。

重要的属性就是sizeCtl，用来控制table的初始化和扩容操作的过程：

● -1代表table正在初始化，其他线程直接join等待。

● -N代表有N-1个线程正在进行扩容操作，严格来说，当其为负数的时候，只用到了低16位，如果低16位为M，此时有M-1个线程进行扩容。

● 大于0有两种情况：如果table没有初始化，她就表示table初始化的大小，如果table初始化完了，就表示table的容量，默认是table大小的四分之三。

Transfer()扩容

table数据转移到nextTable。扩容操作的核心在于数据的转移，把旧数组中的数据迁移到新的数组。ConcurrentHashMap精华的部分是它可以利用多线程来进行协同扩容，简单来说，它把table数组当作多个线程之间共享的任务队列，然后通过维护一个指针来划分每个线程所负责的区间，每个线程通过区间逆向遍历来实现扩容，一个已经迁移完的 Bucket会被替换为一个Forwarding节点，标记当前Bucket已经被其他线程迁移完了。

helpTransfer()帮助扩容

ConcurrentHashMap并发添加元素时，如果正在扩容，其他线程会帮助扩容，也就是多线程扩容。

第一次添加元素时，默认初始长度为16，当往table中继续添加元素时，通过Hash值跟数组长度取余来决定放在数组的哪个Bucket位置，如果出现放在同一个位置，就优先以链表的形式存放，在同一个位置的个数达到了8个以上，如果数组的长度还小于64，就会扩容数组。如果数组的长度大于等于64，就会将该节点的链表转换成树。

通过扩容数组的方式来把这些节点分散开。然后将这些元素复制到扩容后的新数组中，同一个Bucket中的元素通过Hash值的数组长度位来重新确定位置，可能还是放在原来的位置，也可能放到新的位置。而且，在扩容完成之后，如果之前某个节点是树，但是现在该节点的“Key-Value对”数又小于等于6个，就会将该树转为链表。

put()

JDK1.8在使用CAS自旋完成桶的设置时，使用synchronized内置锁保证桶内并发操作的线程安全。尽管对同一个Map操作的线程争用会非常激烈，但是在同一个桶内的线程争用通常不会很激烈，所以使用CAS自旋、synchronized不会降低ConcurrentHashMap的性能。为什么不用ReentrantLock显式锁呢?如果为每 个桶都创建一个ReentrantLock实 例，就会带来大量的内存消耗，反过来，使用CAS自旋、synchronized，内存消耗的增加更小。

get()

get()通过UnSafe的getObjectVolatile()来读取数组中的元素。为什么要这样做?虽然HashEntry数组的引用是volatile类型，但是数组内元素的 用不是volatile类型，因此多线程对 数组元素的修改是不安全的，可能会在数组中读取到尚未构造完成的元素对象。get()方法通过UnSafe的getObjectVolatile方法来保证元素的读取安全，调用getObjectVolatile()去读取数组元素需要先获得元素在数组中的偏移量，在这里，get()方法根据哈希码计算出偏移量为u，然后通过偏移量u来尝试读取数值。
