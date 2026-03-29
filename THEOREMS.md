# Theorem List — All Levels

每个关卡要证明的定理/命题。标注 ✓ 表示已完成，⚠ 表示需要修改，❌ 表示需要新建。

---

## World 1: BasicLean (10 levels) ✓

| # | Title | Statement | Status |
|---|-------|-----------|--------|
| L01 | Rfl tactic | `2 + 2 = 4` | ✓ |
| L02 | Rewrite | `x = 2 → y = 4 → x + x = y` | ✓ |
| L03 | Subset definition | `s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t` | ✓ |
| L04 | Subset transitivity | `r ⊆ s → s ⊆ t → r ⊆ t` | ✓ |
| L05 | Subset reflexivity | `s ⊆ s` | ✓ |
| L06 | Intersection definition | `x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t` | ✓ |
| L07 | Union definition | `x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t` | ✓ |
| L08 | Intersection commutativity | `s ∩ t = t ∩ s` | ✓ |
| L09 | Union associativity | `(s ∪ t) ∪ r = s ∪ (t ∪ r)` | ✓ |
| L10 | Intersection subset | `s ⊆ t → s ∩ t = s` | ✓ |

---

## World 2: BasicFunctions (6 levels) ✓

| # | Title | Statement | Status |
|---|-------|-----------|--------|
| L01 | Injective definition | `Injective f ↔ ∀ x y, f x = f y → x = y` | ✓ |
| L02 | Injective composition | `Injective f → Injective g → Injective (g ∘ f)` | ✓ |
| L03 | Surjective definition | `Surjective f ↔ ∀ y, ∃ x, f x = y` | ✓ ⚠ needs intro |
| L04 | Surjective composition | `Surjective f → Surjective g → Surjective (g ∘ f)` | ✓ |
| L05 | Bijective definition | `Bijective f ↔ Injective f ∧ Surjective f` | ✓ |
| L06 | Bijective composition | `Bijective f → Bijective g → Bijective (g ∘ f)` | ✓ |

---

## World 3: EquivalenceRelation (22 → ~12 levels) ⚠

### Keep (with documentation fixes):

| # | Title | Statement | Status |
|---|-------|-----------|--------|
| L01 | Equality is equivalence (concrete) | `Equivalence (· = · : S → S → Prop)` | ✓ ⚠ doc |
| L02 | Equality is equivalence (general) | `Equivalence (· = · : α → α → Prop)` | ✓ ⚠ doc |
| L03 | Congruence mod n is equivalence | `Equivalence (fun a b => n ∣ (a - b))` | ⚠ needs doc |
| L04 | IsPartition ↔ IsPartition' | `IsPartition C ↔ IsPartition' C` | ✓ |
| L05 | Fiber equivalence | `Equivalence (f · = f ·)` | ⚠ needs doc |
| L06 | Even/Odd is a partition | `IsPartition {{Even}, {Odd}}` | ⚠ needs doc |

### Merge L07-L22 into ~6 levels:

| New # | Title | Merged from | Statement |
|-------|-------|------------|-----------|
| L07 | Symmetry of ≈ | L07 | `x ≈ y ↔ y ≈ x` |
| L08 | Transitivity of ≈ | L08 | `x ≈ y → (x ≈ z ↔ y ≈ z)` |
| L09 | Equivalence class is nonempty | L09+L10 | `x ∈ {y \| x ≈ y}` and `{y \| x ≈ y} ≠ ∅` |
| L10 | Equiv classes form a partition | L11 | `IsPartition' (Set.range (fun x => {y \| x ≈ y}))` |
| L11 | Quotient properties | L12-L17 merged | `quot x = quot y ↔ x ≈ y` |
| L12 | Descent lemma | L22 | `(∀ a b, a ≈ b → f a = f b) → ∀ x, f x = fbar (quot x)` |

### Drop:
- L13 (EquivClass_eq_quote) — technical, not pedagogically essential
- L14 (memEquivClass) — trivial rfl
- L15 (equiv_iff_memsameEquivClass) — subsumed by L11
- L16 (EquivClasseq_of_mem) — subsumed by L11
- L18 (EquivClassNonempty) — subsumed by L09
- L19 (EquivQuot) — subsumed by L11
- L20 (EquivUnquot) — technical
- L21 (unquot_quot_equiv) — technical

---

## World 4: Magma (9 levels) ✓

| # | Title | Statement | Status |
|---|-------|-----------|--------|
| L01 | ℝ₊ is a magma | `Set.isMagma {x : ℝ \| x > 0}` | ✓ |
| L02 | Odd integers not a magma | `¬ Set.isAddMagma {x : ℤ \| Odd x}` | ✓ |
| L03 | Composition is associative | `(f ∘ g) ∘ h = f ∘ (g ∘ h)` | ✓ |
| L04 | Squaring preserves multiplication | `isMulMap (fun x => x * x)` | ✓ |
| L05 | Exp is additive-to-multiplicative | `isAddMulMap Real.exp` | ✓ ⚠ hints |
| L06 | Subtraction is not associative | `∃ a b c, (a-b)-c ≠ a-(b-c)` | ✓ ⚠ hints |
| L07 | Identity is unique | `isIdentity e → isIdentity e' → e = e'` | ✓ |
| L08 | Isomorphism preserves identity | `isIdentity e → isIdentity (φ e)` | ✓ |
| L09 | ℂ ≄* ℝ | `IsEmpty (ℂ ≃* ℝ)` | ✓ |

---

## World 5: GroupBasics (~10 levels) — refactor from BasicGroupTheory L01-L10

| # | Title | Statement | Fraleigh | Status |
|---|-------|-----------|----------|--------|
| L01 | Rewriting with mul_assoc | `h : a*b = b*a → a*b*c = b*(a*c)` | §2 | ✓ |
| L02 | Associativity via `group` | `(a*b)*c = a*(b*c)` | §2 | ✓ |
| L03 | Left inverse is the inverse | `y*x = 1 → y = x⁻¹` | §4 | ✓ |
| L04 | Inverse exists | `∃ b, a*b = 1 ∧ b*a = 1` | §4 | ✓ |
| L05 | Inverse is unique | `a*b=1 → b*a=1 → a*c=1 → c*a=1 → b=c` | §4 | ✓ |
| L06 | Subgroup criterion | `H.Nonempty → (∀ a b ∈ H, a*b⁻¹ ∈ H) → IsSubgroup H` | §5 | ✓ |
| L07 | kℤ is a subgroup | `AddSubgroupClass (SubSetP (· % k = 0)) ℤ` | §6 | ✓ |
| L08 | ℤ/nℤ is a commutative group | `CommGroup (Fin n)` (with explicit add/neg) | §6 | ✓ |
| L09 | Commutator criterion | `a*b = b*a ↔ a*b*a⁻¹*b⁻¹ = 1` | §15 | ✓ |
| L10 | Elementary 2-group is abelian | `(∀ a, a*a=1) → ∀ a b, a*b = b*a` | §4 | ✓ |

---

## World 6: CosetsAndLagrange (~8 levels) — refactor from BasicGroupTheory L11-L18

| # | Title | Statement | Fraleigh | Status |
|---|-------|-----------|----------|--------|
| L01 | Coset membership | `x ∈ g•H ↔ g⁻¹*x ∈ H` | §10 | ✓ |
| L02 | Cosets are equinumerous | `Equiv (g•H) (k•H)` | §10 | ✓ |
| L03 | Coset equality criterion | `g•H = k•H → k⁻¹*g ∈ H` | §10 | ✓ |
| L04 | Coset transitivity | `x ∈ g•H → (y ∈ g•H ↔ x⁻¹*y ∈ H)` | §10 | ✓ |
| L05 | Cosets are disjoint or equal | `(g•H) ∩ (k•H) = ∅ ∨ g•H = k•H` | §10 | ✓ |
| L06 | Klein 4-group not cyclic | `|C|=2 → ¬ IsCyclic (C×C)` | §11 | ✓ |
| L07 | Coset partition (= L05 repeat?) | same as L05 | §10 | ⚠ duplicate |
| L08 | Index and Lagrange | same as L05 | §10 | ⚠ duplicate |

**Note**: L17 and L18 have identical Statements to L15. Need to fix — L17 should be about `|g•H| = |H|` (coset order), L18 about `|G| = [G:H] * |H|` (Lagrange).

---

## World 7: GroupHomo (6 levels) ✓

| # | Title | Statement | Fraleigh | Status |
|---|-------|-----------|----------|--------|
| L01 | f(1) = 1 | `f 1 = 1` | §13 | ✓ |
| L02 | f(a⁻¹) = f(a)⁻¹ | `∀ h, f h⁻¹ = (f h)⁻¹` | §13 | ✓ |
| L03 | Kernel is normal | `x ∈ ker f → g*x*g⁻¹ ∈ ker f` | §14 | ✓ |
| L04 | Normal ↔ coset multiplication | `N.Normal ↔ ∀ g h, (g•N)*(h•N) = (g*h)•N` | §14 | ✓ |
| L05 | Universal property (existence) | `∃! f' : G/N →* H, f' ∘ π = f` | §14 | ✓ |
| L06 | Universal property (uniqueness) | `∃! ψ : P ≃* Q, ψ ∘ πP = πQ` | §14 | ✓ |

---

## World 8: GroupAction (~10 levels) — EXPAND

| # | Title | Statement | Fraleigh | Status |
|---|-------|-----------|----------|--------|
| L01 | Orbit equality | `orbit G x = orbit G y ↔ ∃ g, g•x = y` | §16 | ✓ |
| L02 | Conjugation stabilizer | `conj(g) • stab(x) = stab(g•x)` | §16 | ✓ |
| L03 | Orbit-Stabilizer theorem | `G/stab(x) ≃ orbit(x)` | §16.16 | ✓ |
| L04 | Action on cosets | G acts on G/H | §16 | ❌ new |
| L05 | Conjugation action, center | conjugacy classes, Z(G) | §16 | ❌ new |
| L06 | Fixed point counting | `|X| ≡ |X^G| (mod p)` for p-groups | §36.1 | ❌ new |
| L07 | Cauchy's theorem | `p ∣ |G| → ∃ a, orderOf a = p` | §36.3 | ❌ new |
| L08 | Normalizer definition | `N[H] = {g | gHg⁻¹ = H}` | §36.5 | ❌ new |
| L09 | Normalizer lemma | `(N[H]:H) ≡ (G:H) (mod p)` | §36.6 | ❌ new |
| L10 | Class equation | `|G| = |Z(G)| + Σ [G:C_G(gi)]` | §37.2 | ❌ new |

---

## World 9: Sylow (~8 levels) — NEW

| # | Title | Statement | Fraleigh | Status |
|---|-------|-----------|----------|--------|
| L01 | p-subgroup definition | `IsPGroup p H ↔ ∀ h ∈ H, orderOf h is power of p` | §36.4 | ❌ new |
| L02 | First Sylow Theorem | `p^n ∣ |G| → ∃ H ≤ G, |H| = p^n` | §36.8 | ❌ new |
| L03 | Second Sylow Theorem | `IsSylow p P → IsSylow p Q → ∃ g, gPg⁻¹ = Q` | §36.10 | ❌ new |
| L04 | Third Sylow Theorem | `#{Sylow p-subgroups} ≡ 1 (mod p)` and divides `|G|` | §36.11 | ❌ new |
| L05 | Center of p-group nontrivial | `IsPGroup p G → Z(G) ≠ {1}` | §37.4 | ❌ new |
| L06 | Groups of order p² abelian | `|G| = p² → IsCommutative G` | §37.6 | ❌ new |
| L07 | No simple group of order 12 | application | §37 | ❌ new |
| L08 | Classify groups of small order | application | §37 | ❌ new |

---

## Summary

| World | Levels | Status |
|-------|--------|--------|
| BasicLean | 10 | ✓ done |
| BasicFunctions | 6 | ✓ mostly done |
| EquivalenceRelation | 22→12 | ⚠ needs merge+doc |
| Magma | 9 | ✓ mostly done |
| GroupBasics | 10 | ⚠ refactor from BGT |
| CosetsAndLagrange | 8 | ⚠ fix duplicates L17/L18 |
| GroupHomo | 6 | ✓ done |
| GroupAction | 3→10 | ❌ 7 new levels |
| Sylow | 0→8 | ❌ all new |
| **Total** | **~79** | |
