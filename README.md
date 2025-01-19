# ProbMonad 基于单子理论定义概率程序并证明基本性质 #

## 环境 

与课程环境配置类似，详见 [课程仓库](https://bitbucket.org/WxWyashen/cs2612-2024fall)。

## 项目内容和结构

- `ListOperation/ListOperation.v`：定义了一些关于列表的操作、谓词和引理。主要包括：
    - `filter_dup`：过滤 `list` 中的重复元素，以及相关性质。
    - `perm_filter_dup`：两个 `list` 在 `filter_dup` 之后互为 `Permutation` 的相关性质。
    - `NoDup`：补充标准库中 `NoDup` 的相关性质
    - `perm_after_map`：两个 `list` 在 `map` 之后互为 `Permutation` 的相关性质。
    - `Forall2`：补充标准库中 `Forall2` 的相关性质
    - `combine`：补充标准库中 `combine` 的相关性质
    - `list_partition_permutation`：将一个或一对 `list` 按照给定的要求进行分割和重排的相关性质。
    - `sum_prob`：`sum` 的定义、性质和相关引理。
    - `misc`：一些其他引理。
- `ProbMonad.v`：定义了概率单子 `ProbMonad`，并证明了其满足单子定律。主要包括：
    - `Monad`：单子的定义（已经在课程中给出）。
    - `SetMonad`：集合单子的定义（已经在课程中给出）和相关性质。
    - `ProbDistr`：概率分布的定义和相关性质。包括：
        - `ProbDistr`：概率分布的定义。
        - `legal`：判定概率分布是否合法。
        - `equiv`：概率分布的等价性。
        - `is_det`：判定概率分布是否为确定性分布（只含有一个元素，概率为 1 的分布）。
        - `sum_distr`：将一列概率分布按照给定的权重进行加权求和，得到一个新的概率分布。
        - `compute_pr`：计算 `ProbDistr Prop` 中满足给定性质的概率。
        - `imply_event` 和 `equiv_event`：两个 `ProbDistr Prop` 之间的蕴含和等价关系。证明这种蕴含/等价关系满足自反、传递、对称和其他相关性质；证明了 `imply_event` 对于 `compute_pr` 的单调性。
    - `ProbMonad`：概率单子的定义和相关性质。包括：
        - `ProbMonad`：概率单子的 `bind` 和 `ret` 操作的定义；定义了 `ProbMonad` 是概率分布的集合。
        - `legal`：判定概率单子是否合法。证明了 `ProbMonad` 的 `bind` 和 `ret` 操作合法。声明了 `ProbMonad` 是 `Monad` 的实例。
        - `equiv`：概率单子的等价性。
        - `compute_pr`：定义对于 `ProbMonad Prop` 求概率的操作。
        - `imply_event` 和 `equiv_event`：两个 `ProbMonad Prop` 之间的蕴含和等价关系。证明这种蕴含/等价关系满足自反、传递、对称和其他相关性质；证明了 `imply_event` 对于 `compute_pr` 的单调性。证明了这种蕴含/等价关系与 `ProbMonad` 的 `bind` 和 `ret` 操作的关系。
        - 证明了 `ProbMonad` 的 `bind` 的结合律、`ret` 是 `bind` 的左右单位元。

## 完成情况

对于初始给出的相关定义和所有要求证明的性质，均已完成证明。部分定义的修改已经和 TA 与老师讨论过并得到确认。

所有要求证明的性质都以 `Level ?` 注释标记。

## 使用的库和公理

除了常用标准库和 `SetsClass` 外，我们使用了以下额外的库和公理：

- `Axiom eq_dec`：认为任意类型的相等性判定是可判定的。这有助于判定 `list` 中是否含有重复元素，被用于 `filter_dup` 的定义和证明。
- `Coq.Lists.ListSet`：用于 `filter_dup` 的定义和性质。该标准库提供了一个基于 `list` 的集合的定义和插入、删除等操作和性质。
- `Coq.Logic.FunctionalExtensionality`：用于函数的相等性判定。这有助于我们 `rewrite` 一些求值行为相同的函数。

        