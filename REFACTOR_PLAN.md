# Custom Definitions vs Mathlib — Replacement Plan

## 审计结果

### Lemmas/Group.lean — Magma 世界的基础定义

| 自定义 | Mathlib 对应 | 建议 |
|--------|-------------|------|
| `Mul.isIdentity` | 无直接对应（Mathlib 用 typeclass `One`） | **保留** — 这是 Magma 世界的教学定义，用于让学生理解"单位元"是一个性质而非内置结构。Mathlib 的 `One` 是 typeclass，对初学者太抽象。 |
| `Mul.isMulMap` | `MonoidHom`（`→*`）| **保留** — 简单的谓词定义 `∀ x y, f(x*y) = f(x)*f(y)` 比 `MonoidHom` 的 bundled morphism 更容易理解。Magma 世界的目的是让学生理解"保持运算"的概念。后面 GroupHomo 世界再用 `→*`。 |
| `Set.isMagma` | 无直接对应 | **保留** — Magma（原群）不是 Mathlib 的核心概念，但对教学有价值：它是"群"的最简单前身。 |
| `Set.IsMagma` (class) | 无 | **保留** — 配套 `isMagma` |
| `Set.isMulAssoc` | 无直接对应 | **保留** — 教学用 |
| `Set.IsSemigroup`, `HasOne`, `IsMonoid` | `Submonoid`, `Subgroup` 等 | **保留但标注** — 这些在 Group.lean 中定义但大部分被注释掉了（`/- ... -/`），不影响构建。可以后续清理。 |

**结论：Magma 世界的自定义定义全部保留。** 这个世界的教学目标是让学生从零开始理解代数结构（运算、封闭、结合律、单位元），而不是直接用 Mathlib 的高度抽象 typeclass 体系。

---

### Lemmas/GroupTheory.lean — 群论引理

| 自定义 | Mathlib 对应 | 建议 |
|--------|-------------|------|
| `Monoid.instHMulSet` (Set 的乘法) | `Mathlib.Algebra.Group.Pointwise.Set.Basic` 中的 `Set.mul` | **替换** — Mathlib 已有 `open scoped Pointwise` 后 `Set` 自动有 `*` 运算。自定义的 `instHMulSet` 和 `Monoid.instSet` 可能与 Mathlib 冲突。 |
| `Set.mem_mul_set_iff` | `Set.mem_mul` (在 Pointwise 中) | **替换** — 用 Mathlib 的 |
| `GroupHom.intro` | `MonoidHom.mk'` | **替换** — `MonoidHom.mk'` 做完全一样的事（从 `map_mul` 自动推导 `map_one`）。目前 `GroupHom.intro` 还有自己的 `map_one'` 证明。 |
| `MulEquiv.intro` | `MulEquiv.mk` 或直接构造 | **替换** — 用 Mathlib 标准构造 |
| `Subgroup.mem_of_inv_mul_mem` | 可用 `Subgroup.mul_mem` + `Subgroup.inv_mem` 组合 | **保留为教学引理** — 名字更直观 |
| `Subgroup.mem_coset_iff_diff_mem_subgroup` | `QuotientGroup.leftRel_apply` 或相关 | **保留** — 专为 Coset 世界设计的引理，比 Mathlib 的更直接 |

---

### Lemmas/Partition.lean — 等价关系世界

| 自定义 | Mathlib 对应 | 建议 |
|--------|-------------|------|
| `IsPartition` | `Setoid.IsPartition`（`Mathlib.Data.Setoid.Partition`）| **替换** — 定义完全一样！直接用 Mathlib 的。 |
| `IsPartition'` | 无直接对应 | **保留** — 这是第二种分划定义（∅∉c ∧ ⋃₀c=univ ∧ pairwise disjoint），用于教学。证明它和 `IsPartition` 等价是一个教学关卡。 |
| `Setoid.Equivclass` | `Quotient` / `Setoid.classes` | **考虑替换** — Mathlib 用 `Quotient s` 作为商集，`Setoid.classes` 作为等价类集合。但我们的 `Equivclass` 是 `{c : Set α // ∃ x, c = {y | x ≈ y}}`，一个 subtype。这比 `Quotient` 更"具体"——学生能看到等价类就是一个集合。**建议：保留作为教学包装，但加注释说明与 `Quotient` 的关系。** |
| `Setoid.quot` | `Quotient.mk` | **保留作为包装** — `quot x` 返回 `Equivclass`，是对 `{y | x ≈ y}` 的包装。比 `Quotient.mk` 更直观。 |
| `Setoid.equivclass_eq_iff_equiv` 等引理 | `Quotient.eq` 等 | **保留** — 这些引理是为 `Equivclass` 类型写的，与 Mathlib 的 `Quotient` 引理不兼容。 |

---

### GroupBasics 世界

| 自定义 | Mathlib 对应 | 建议 |
|--------|-------------|------|
| `IsSubgroup` (L06) | `Subgroup` | **替换** — `Subgroup` 是 Mathlib 的核心结构。`IsSubgroup` 来自已删除的 `Mathlib.Deprecated.Subgroup`。改用 `Subgroup.ofDiv`（子群判据：非空 + a*b⁻¹ 封闭）。 |
| `subgroup_make` / `addsubgroup_make` (L07) | `Subgroup.ofDiv` / `AddSubgroup.ofSub` | **替换** — Mathlib 已有。 |
| `SubSetP` (L07) | `Subgroup` + `AddSubgroup` | **替换** — 自定义的 `SubSetP` 太特殊。 |
| `CommGroup_mk` (L08) | 直接构造 `CommGroup.mk` | **保留为教学辅助** — 包装了 `CommGroup` 的构造器，让学生按"加法、零、负、结合律、逆、交换律"的顺序逐步填写。比直接用 `CommGroup.mk` 更有引导性。 |

---

## 替换优先级

### 高优先级（应该替换）

1. **`IsPartition` → `Setoid.IsPartition`**
   - 定义完全一样，直接 `import Mathlib.Data.Setoid.Partition` 替换
   - 影响：Partition.lean, L04, L05, L06, L10, L11

2. **`IsSubgroup` → `Subgroup.ofDiv`**
   - L06 的 Statement 改为证明 `Subgroup.ofDiv` 的应用
   - 教学价值不变：学生仍然证明"非空 + a*b⁻¹ 封闭 → 子群"

3. **`GroupHom.intro` → `MonoidHom.mk'`**
   - GroupHomo 世界已经用了 `→*`，没有理由还保留自定义构造器

4. **`Monoid.instHMulSet` → Pointwise**
   - 可能与 Mathlib 实例冲突，应该替换

### 低优先级（保留）

5. **Magma 世界的所有自定义定义** — 保留
   - `isIdentity`, `isMulMap`, `isMagma` 等
   - 教学目标是从零开始理解代数结构

6. **`Equivclass` / `quot`** — 保留作为教学包装
   - 比 `Quotient` 更直观
   - 加注释说明关系

7. **`CommGroup_mk`** — 保留
   - 教学辅助，引导学生理解群公理

8. **`Subgroup.mem_coset_iff_diff_mem_subgroup`** — 保留
   - 比 Mathlib 的表述更教学友好

---

## 不替换的理由

| 保留的定义 | 理由 |
|-----------|------|
| Magma 世界定义 | 教学目标是让学生**从零构建**代数结构概念，而非使用现成的 typeclass |
| `Equivclass` | 比 `Quotient` 更具体：等价类就是一个集合，而非抽象的商类型 |
| `IsPartition'` | 第二种分划定义是教学内容的一部分 |
| `CommGroup_mk` | 引导式构造器，帮助学生逐步验证群公理 |
| Coset 引理 | 针对教学场景的表述，比 Mathlib 的更直接 |
