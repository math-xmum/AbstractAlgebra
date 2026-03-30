# Theorem List — All Levels

设计原则：
1. **具体例子先行** — 每个世界前几关在具体对象上操作，建立直觉
2. **每关一个概念** — 不在一关里引入多个新东西
3. **理解对象 > 证明技巧** — 学生要理解群/子群/陪集是什么，而不只是操作 tactic
4. **循序渐进** — 从计算到定义到抽象证明
5. **每个证明 ≤ 20 tactic**

✓ = 已完成  ⚠ = 需修改  ❌ = 需新建  🔄 = 需重写

---

## World 1: BasicLean (10 levels) ✓

教学目标：熟悉 Lean 和 game 界面，学会基本 tactic。

| # | 教学目标 | Statement | tactic 引入 |
|---|---------|-----------|------------|
| L01 | 熟悉界面 | `2 + 2 = 4` | rfl, norm_num |
| L02 | 等式改写 | `x = 2 → y = 4 → x + x = y` | rw |
| L03 | 定义展开 | `s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t` | rfl (定义) |
| L04 | 链式推理 | `r ⊆ s → s ⊆ t → r ⊆ t` | intro |
| L05 | 简单证明 | `s ⊆ s` | exact |
| L06 | 认识 ∧ | `x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t` | rfl |
| L07 | 认识 ∨ | `x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t` | rfl |
| L08 | 集合相等 | `s ∩ t = t ∩ s` | ext, constructor |
| L09 | 综合练习 | `(s ∪ t) ∪ r = s ∪ (t ∪ r)` | left, right |
| L10 | 综合练习 | `s ⊆ t → s ∩ t = s` | simp |

---

## World 2: BasicFunctions (6 levels) ✓

教学目标：理解映射的单射/满射/双射概念。

| # | 教学目标 | Statement | 新概念 |
|---|---------|-----------|-------|
| L01 | 认识单射定义 | `Injective f ↔ ∀ x y, f x = f y → x = y` | 单射 |
| L02 | 单射的复合 | `Injective f → Injective g → Injective (g ∘ f)` | unfold, apply |
| L03 | 认识满射定义 | `Surjective f ↔ ∀ y, ∃ x, f x = y` | 满射 |
| L04 | 满射的复合 | `Surjective f → Surjective g → Surjective (g ∘ f)` | obtain, use |
| L05 | 认识双射定义 | `Bijective f ↔ Injective f ∧ Surjective f` | 双射 |
| L06 | 双射的复合 | `Bijective f → Bijective g → Bijective (g ∘ f)` | constructor |

---

## World 3: EquivalenceRelation (~12 levels) 🔄

教学目标：理解等价关系如何把集合分成等价类，为商群做准备。

### Part A: 等价关系是什么（具体例子）

| # | 教学目标 | Statement | 新概念 |
|---|---------|-----------|-------|
| L01 | 等号是等价关系 | `Equivalence (· = · : S → S → Prop)` | 等价关系三条件 |
| L02 | 等号是等价关系（一般） | `Equivalence (· = · : α → α → Prop)` | 类型变量 |
| L03 | 模 n 同余是等价关系 | `Equivalence (fun a b => n ∣ (a-b))` | 整除, 同余 |
| L04 | 纤维等价关系 | `Equivalence (f · = f ·)` | 纤维 |

### Part B: 等价关系与分划

| # | 教学目标 | Statement | 新概念 |
|---|---------|-----------|-------|
| L05 | 偶数/奇数是一个分划 | `IsPartition {{Even}, {Odd}}` | 分划 |
| L06 | 分划两种定义等价 | `IsPartition C ↔ IsPartition' C` | push_neg |

### Part C: 等价类与商集

| # | 教学目标 | Statement | 新概念 |
|---|---------|-----------|-------|
| L07 | 对称性 | `x ≈ y ↔ y ≈ x` | Setoid |
| L08 | 传递性改写 | `x ≈ y → (x ≈ z ↔ y ≈ z)` | replace |
| L09 | 等价类非空 | `x ∈ {y \| x ≈ y}` 和 `{y \| x ≈ y} ≠ ∅` | 等价类 |
| L10 | 等价类构成分划 | `IsPartition' (Set.range (fun x => {y \| x ≈ y}))` | 等价类=分划 |
| L11 | 商等于等价类 | `quot x = quot y ↔ x ≈ y` | 商集 |
| L12 | 下降引理 | `(∀ a b, a ≈ b → f a = f b) → f = fbar ∘ quot` | 商映射 |

---

## World 4: Magma (9 levels) ✓

教学目标：从最简单的代数结构开始，理解"运算+性质"的思想。

| # | 教学目标 | Statement | 新概念 |
|---|---------|-----------|-------|
| L01 | 正实数对乘法封闭 | `Set.isMagma {x : ℝ \| x > 0}` | 原群(magma) |
| L02 | 奇数对加法不封闭 | `¬ Set.isAddMagma {x : ℤ \| Odd x}` | 反例 |
| L03 | 函数复合的结合律 | `(f ∘ g) ∘ h = f ∘ (g ∘ h)` | 结合律 |
| L04 | 平方映射保持乘法 | `isMulMap (fun x => x * x)` | 同态映射 |
| L05 | exp 是加法到乘法的同态 | `isAddMulMap Real.exp` | 经典例子 |
| L06 | 减法不满足结合律 | `∃ a b c, (a-b)-c ≠ a-(b-c)` | 反例构造 |
| L07 | 单位元的唯一性 | `isIdentity e → isIdentity e' → e = e'` | 单位元 |
| L08 | 同构保持单位元 | `isIdentity e → isIdentity (φ e)` | 同构 |
| L09 | ℂ 和 ℝ 乘法不同构 | `IsEmpty (ℂ ≃* ℝ)` | 非同构证明 |

---

## World 5: GroupBasics (~12 levels) 🔄

教学目标：理解群是什么——从具体群出发，然后学习抽象群的性质。

### Part A: 认识群（具体例子）

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L01 | 在具体群上计算 | `(a*b)*c = a*(b*c)` 用 `group` | 群公理 | ✓ |
| L02 | ℤ/nℤ 是交换群 | `CommGroup (Fin n)` | 具体群构造 | ✓ |
| L03 | 逆元存在 | `∃ b, a*b = 1 ∧ b*a = 1` | 逆元 | ✓ |

### Part B: 群的基本性质

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L04 | 左逆 = 逆 | `y*x = 1 → y = x⁻¹` | 逆元唯一性 | ✓ |
| L05 | 逆元唯一 | `a*b=1 → b*a=1 → a*c=1 → c=a=1 → b=c` | mul_left_cancel | ✓ |
| L06 | 交换子判据 | `a*b = b*a ↔ a*b*a⁻¹*b⁻¹ = 1` | 交换子 | ✓ |
| L07 | 2-阶元群是交换群 | `(∀ a, a*a=1) → ∀ a b, a*b = b*a` | 阶 | ✓ |

### Part C: 子群

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L08 | 子群判据 | `H.Nonempty → (∀ a b ∈ H, a*b⁻¹ ∈ H) → IsSubgroup H` | 子群 | ✓ |
| L09 | kℤ 是 ℤ 的子群 | `AddSubgroupClass (SubSetP (· % k = 0)) ℤ` | 具体子群 | ✓ |
| L10 | Klein 四元群不是循环群 | `\|C\|=2 → ¬ IsCyclic (C×C)` | 循环群 | ✓ |

---

## World 6: CosetsAndLagrange (~8 levels) 🔄

教学目标：理解陪集把群"切割"成等大的块，从而得到 Lagrange 定理。

### Part A: 认识陪集（具体例子）

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L01 | 陪集成员判据 | `x ∈ g•H ↔ g⁻¹*x ∈ H` | 左陪集 | ✓ |
| L02 | 陪集等势 | `Equiv (g•H) (k•H)` | 陪集大小 | ✓ |

### Part B: 陪集的性质

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L03 | 陪集相等判据 | `g•H = k•H → k⁻¹*g ∈ H` | 陪集相等 | ✓ |
| L04 | 陪集是轨道 | `x ∈ g•H → (y ∈ g•H ↔ x⁻¹*y ∈ H)` | 传递性 | ✓ |
| L05 | 陪集不交或相等 | `(g•H) ∩ (k•H) = ∅ ∨ g•H = k•H` | 分划 | ✓ |

### Part C: Lagrange 定理

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L06 | 陪集大小 = 子群阶 | `Nat.card (g•H) = Nat.card H` | \|gH\|=\|H\| | ⚠ fix |
| L07 | Lagrange 定理 | `\|G\| = [G:H] * \|H\|` | Lagrange | ⚠ fix |
| L08 | 阶整除群阶 | `orderOf a ∣ Nat.card G` | 推论 | ❌ new |

---

## World 7: GroupHomo (6 levels) ✓

教学目标：理解同态是"保持结构的映射"，核和商群的概念。

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L01 | 同态保持单位元 | `f 1 = 1` | 同态 | ✓ |
| L02 | 同态保持逆元 | `∀ h, f h⁻¹ = (f h)⁻¹` | | ✓ |
| L03 | 核是正规子群 | `x ∈ ker f → g*x*g⁻¹ ∈ ker f` | 核, 正规 | ✓ |
| L04 | 正规 ↔ 陪集可乘 | `N.Normal ↔ ∀ g h, (g•N)*(h•N) = (g*h)•N` | 商群运算 | ✓ |
| L05 | 商群的万有性质 | `∃! f' : G/N →* H, f' ∘ π = f` | 万有性质 | ✓ |
| L06 | 万有性质的唯一性 | `∃! ψ : P ≃* Q, ψ ∘ πP = πQ` | | ✓ |

---

## World 8: GroupAction (~10 levels) 🔄

教学目标：群作用是理解群结构的核心工具。从具体例子到抽象定理，最终为 Sylow 做准备。

### Part A: 认识群作用（具体例子）

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L01 | 轨道相等判据 | `orbit G x = orbit G y ↔ ∃ g, g•x = y` | 轨道 | ✓ |
| L02 | 共轭作用与稳定子 | `conj(g)•stab(x) = stab(g•x)` | 共轭, 稳定子 | ✓ |
| L03 | 轨道-稳定子定理 | `G/stab(x) ≃ orbit(x)` | 核心定理 | ✓ |

### Part B: 群作用在陪集上

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L04 | 群作用在陪集上 | G 左乘作用在 G/H 上是传递的 | 陪集作用 | ❌ |
| L05 | 共轭类与中心 | `Z(G) = {g \| 共轭类为 {g}}` | 中心 | ❌ |

### Part C: p-群的不动点定理（Sylow 的关键工具）

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L06 | p-群的不动点计数 | `\|X\| ≡ \|X^G\| (mod p)` | 不动点 | ❌ |
| L07 | Cauchy 定理 | `p ∣ \|G\| → ∃ a, orderOf a = p` | Cauchy | ❌ |

### Part D: 正规化子

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L08 | 正规化子定义 | `N[H] = {g \| gHg⁻¹ = H}` | 正规化子 | ❌ |
| L09 | 正规化子引理 | `(N[H]:H) ≡ (G:H) (mod p)` | 关键引理 | ❌ |
| L10 | 类方程 | `\|G\| = \|Z(G)\| + Σ [G:C_G(gi)]` | 类方程 | ❌ |

---

## World 9: Sylow (~8 levels) ❌

教学目标：Sylow 定理是有限群论的核心工具，所有证明都通过群作用完成。

### Part A: 定义与 Sylow 第一定理

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L01 | Sylow p-子群定义 | p-子群, Sylow p-子群的定义 | 定义 | ❌ |
| L02 | Sylow I: 存在性 | `p^n ∣ \|G\| → ∃ H ≤ G, \|H\| = p^n` | 存在 | ❌ |

### Part B: Sylow 第二、第三定理

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L03 | Sylow II: 共轭性 | 所有 Sylow p-子群共轭 | 共轭 | ❌ |
| L04 | Sylow III: 计数 | `n_p ≡ 1 (mod p)` 且 `n_p ∣ \|G\|` | 计数 | ❌ |

### Part C: 应用

| # | 教学目标 | Statement | 新概念 | Status |
|---|---------|-----------|-------|--------|
| L05 | p-群的中心非平凡 | `IsPGroup p G → Z(G) ≠ {1}` | 推论 | ❌ |
| L06 | p² 阶群是交换群 | `\|G\| = p² → IsCommutative G` | 推论 | ❌ |
| L07 | 不存在 12 阶单群 | 用 Sylow III 排除 | 应用 | ❌ |
| L08 | 小阶群分类 | 分类 15 阶以下的群 | 综合 | ❌ |

---

## 总结

| World | levels | 新概念 | 教学重点 |
|-------|--------|-------|---------|
| BasicLean | 10 | Lean tactic | 工具 |
| BasicFunctions | 6 | 单射/满射/双射 | 映射 |
| EquivalenceRelation | 12 | 等价关系/商集 | 等价 |
| Magma | 9 | 运算/封闭/结合律 | 代数结构 |
| GroupBasics | 12 | 群/逆元/子群 | **理解群** |
| CosetsAndLagrange | 8 | 陪集/Lagrange | **理解商** |
| GroupHomo | 6 | 同态/核/商群 | **结构保持** |
| GroupAction | 10 | 群作用/轨道/不动点 | **核心工具** |
| Sylow | 8 | Sylow 定理 | **最终目标** |
| **Total** | **~81** | | |
