# E894 新实现：C 同团队全文复核

2026-09-20。结论：**PASS，未发现本次目标的语义遗漏或三份受审源码的证明阻断。** 实际全文阅读 `Growth.lean`、`Rotation.lean`、`Main.lean`，逐步重构证明，并实际编译下述独立类型检查文件。没有修改这三份受审源码。

参与披露：C 是 `Coloring.lean` 的作者，且已知本项目的整体证明设计和先行形式化。本次是对另外三份文件的非作者、同团队复核，不是整个工程的完全独立或外部审核。新源码不声称独立发现、首次形式化、官方接受或奖金资格；既有 PR344 等先行仍按 STATUS.md 披露。

## 受审身份

| 文件 | 字节 | SHA256 |
|---|---:|---|
| Growth.lean | 2009 | `00ba496af543f73d185ce4efc6a22d2f68466231bb8f2d541c5ae1738abd387d` |
| Rotation.lean | 4259 | `2a7e0e100f26bef8e5fb3be47b6ed6eff281578705ac7d2379a7d3181df8c6f0` |
| Main.lean | 2423 | `5130ed68d12294fc324a6138e2c9c64a911666064cb2d4f20a6fb0055328e761` |
| Coloring.lean（C所写依赖） | 2006 | `a0945ff76d0552bd14fd0b14d5d6fe9dc37e2590c5d6458d5aa4a6a97df031d4` |
| ProbeReviewC.lean | 1020 | `55f6af13ec315ee213c85acced84b19c50e528cfb6ee2447bc447d78f9947de9` |

## 实际数学和范围复核

1. **Growth：任意正增长率。** `iterated_growth` 对步数归纳，使用正乘子 `1+ε`，保留所有起始索引 k。`exists_stride` 取自然数 `r>3/ε`，由 Bernoulli 不等式得到 `(1+ε)^r≥4`，并排除 r=0。没有要求 ε 为有理数、ε≥某个固定常数，或序列在有限范围内。自然数值保证乘法保持不等式。`stride_subsequence` 对任意 j 将 `r*j+i` 的 r 步增长转换为子序列一步增长，未丢弃首项。

2. **Rotation：一个 θ 同时处理无穷多项。** `next_interval` 取 `z=ceil(q*a−1/4)`，得到新闭区间左端≥a，右端严格小于 `a+3/(2q)`，再由 q≥4p 控制在旧区间宽度 `1/(2p)` 内。`intervalLabel` 的递归表达与此代入一致。上下端点分别单调递增/递减；证明了任意两个索引 j,k 都有 `lower j≤upper k`，而不只同索引有序。`sSup(range lower)` 的非空与有上界前提均实际供应，因此同一个 θ 位于全部闭区间。`hpos` 保证所有除数严格正；1/4及3/4端点都保留。

3. **Main：完整 ℤ 上的单个有限染色。** 固定 stride r 后，对每个 `i : Fin r` 一次性选择 θ_i 和四染色，再取有限乘积 `Fin r → Fin 4`，通过等价编码为 `Fin N`。`N=Fintype.card C>0`；数学上其大小为 `4^r`，不随所考察的顶点或序列项改变。染色域是真正的 `ℤ`，不是自然数、有限区间或稠密子集。

4. **所有序列项的索引。** 对任意 k，取 `i=k%r`、`j=k/r`。`Nat.mod_add_div` 实际证明 `r*j+i=k`，包含 k=0 和所有余数类。把 `y−x=a k` 代入该子序列的中半区间条件后，调用四染色接口时顺序为 `y,x`，与接口中的 `x−y` 正确对应。最后将相等颜色的向量投影到 i 坐标并取对称等式，矛盾方向正确。

5. **没有额外几何或条件接口。** 顶层只假设正整数序列，以及存在一个统一 ε>0 使每个相邻项满足增长界；没有假设事先存在 θ、有限着色、某个强子序列供应或待证外部组合定理。θ和染色均由新源码构造/选择。正性是本次原定目标的一部分，不能允许差值0。

## 实际类型与公理检查

`ProbeReviewC.lean` 导入 Main，并另证等价的无向距离接口：

`∃ N>0, ∃ c : ℤ → Fin N, ∀ x y k, |x−y|=(a k : ℤ) → c x≠c y`。

该包装只按 x≤y 或 y≤x 分情况，使用顶层定理的两个次序；没有增加假设。这实际验证了正差表述覆盖全部无向禁用距离，而非遗漏负整数或反向配对。

本轮执行 `python -B -X utf8 e894-independent/compile.py ProbeReviewC.lean`，进程 **exit 0**。使用项目已准备的 Lean 4.19.0 和已编译模块；输出的五个声明

- `GottL894.iterated_growth`
- `GottL894.exists_stride`
- `GottL894.exists_rotation`
- `GottL894.lacunary_difference_coloring`
- `GottL894.reviewC_absolute_difference`

其 `#print axioms` 全部仅为 `[propext, Classical.choice, Quot.sound]`。没有 `sorryAx`、额外数学公理或 `native_decide` 的编译信任公理出现在这些实际输出中。`compile.py` 本轮读取身份为1172 B、SHA256 `6b53060e991ddbb2d4eb303fb58014c8854162d193f695eee60e8ce6096321cc`。

## 验证边界

这次 Probe 导入团队已实际编译的 Growth/Rotation/Coloring/Main 对象；本次新增实际运行是 Probe 的类型检查和公理输出，不声称重新从零构建所有依赖。现有 Mathlib 及其他包缓存只读复用，未独立重建或回放其完整闭包，也没有运行不同实现的外部检查器。因此 PASS 指本次源码范围及本地 Lean 验证，不是官方审核或完整供应链认证。未修改公共仓库、历史资料或全局权威状态。
