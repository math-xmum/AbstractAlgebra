import GameServer.Commands

import Game.Levels.Lemmas.GroupTheory
import Game.Levels.Lemmas.Partition

import Mathlib.Tactic.Common

import Game.Generator.Basic

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file lean file per world
that imports all its levels.
-/

/-! ## TheoremDoc and DefinitionDoc entries -/

-- ==================== Category "Group" ====================

/-- `(a * b) * c = a * (b * c)` -/
TheoremDoc mul_assoc as "mul_assoc" in "Group"

/-- `a * 1 = a` -/
TheoremDoc mul_one as "mul_one" in "Group"

/-- `1 * a = a` -/
TheoremDoc one_mul as "one_mul" in "Group"

/-- `a * a⁻¹ = 1` -/
TheoremDoc mul_inv_cancel as "mul_inv_cancel" in "Group"

/-- `a * b = a * c → b = c` -/
TheoremDoc mul_left_cancel as "mul_left_cancel" in "Group"

/-- `b * a = c * a → b = c` -/
TheoremDoc mul_right_cancel as "mul_right_cancel" in "Group"

/-- `b * a = c * a ↔ b = c` -/
TheoremDoc mul_right_cancel_iff as "mul_right_cancel_iff" in "Group"

/-- `a * b = a ↔ b = 1` -/
TheoremDoc mul_eq_left as "mul_eq_left" in "Group"

/-- `a * b = 1 ↔ b = a⁻¹` -/
TheoremDoc mul_eq_one_iff_eq_inv as "mul_eq_one_iff_eq_inv" in "Group"

/-- `a * b = 1 ↔ a⁻¹ = b` -/
TheoremDoc mul_eq_one_iff_inv_eq as "mul_eq_one_iff_inv_eq" in "Group"

/-- `(a⁻¹)⁻¹ = a` -/
TheoremDoc inv_inv as "inv_inv" in "Group"

/-- `0 < a → 0 < b → 0 < a * b` -/
TheoremDoc mul_pos as "mul_pos" in "Group"

/-- Construct `P ∧ Q` from proofs of `P` and `Q` -/
TheoremDoc And.intro as "And.intro" in "Group"

/-- `(a + b) + c = a + (b + c)` -/
TheoremDoc add_assoc as "add_assoc" in "Group"

/-- `a + b = b + a` -/
TheoremDoc add_comm as "add_comm" in "Group"

/-- `a + b = 0 ↔ b = -a` -/
TheoremDoc add_eq_zero_iff_eq_neg as "add_eq_zero_iff_eq_neg" in "Group"

/-- `a + b = 0 ↔ -a = b` -/
TheoremDoc add_eq_zero_iff_neg_eq as "add_eq_zero_iff_neg_eq" in "Group"

-- ==================== Category "Subgroup" ====================

/-- Construct a subgroup from nonemptiness and `a * b⁻¹` closure -/
TheoremDoc Subgroup.ofDiv as "Subgroup.ofDiv" in "Subgroup"

/-- `1 ∈ H` for any subgroup `H` -/
TheoremDoc Subgroup.one_mem as "Subgroup.one_mem" in "Subgroup"

/-- `a ∈ H → b ∈ H → a * b ∈ H` -/
TheoremDoc Subgroup.mul_mem as "Subgroup.mul_mem" in "Subgroup"

/-- `a ∈ H → a⁻¹ ∈ H` -/
TheoremDoc Subgroup.inv_mem as "Subgroup.inv_mem" in "Subgroup"

/-- `a ∈ H → b ∈ H → a⁻¹ * b ∈ H` -/
TheoremDoc Subgroup.mem_of_inv_mul_mem as "Subgroup.mem_of_inv_mul_mem" in "Subgroup"

/-- `a ∈ H → b ∈ H → a * b⁻¹ ∈ H` -/
TheoremDoc Subgroup.mem_of_mem_mul_inv as "Subgroup.mem_of_mem_mul_inv" in "Subgroup"

/-- `y ∈ g • H ↔ x⁻¹ * y ∈ H` when `x ∈ g • H` -/
TheoremDoc Subgroup.mem_coset_iff_diff_mem_subgroup as "Subgroup.mem_coset_iff_diff_mem_subgroup" in "Subgroup"

/-- `|H|` divides `|G|` for subgroup `H ≤ G` -/
TheoremDoc Subgroup.card_subgroup_dvd_card as "Subgroup.card_subgroup_dvd_card" in "Subgroup"

/-- `|G| = [G : H] * |H|` -/
TheoremDoc Subgroup.card_eq_card_quotient_mul_card_subgroup as "Subgroup.card_eq_card_quotient_mul_card_subgroup" in "Subgroup"

/-- `a ∈ g • H ↔ g⁻¹ * a ∈ H` -/
TheoremDoc mem_leftCoset_iff as "mem_leftCoset_iff" in "Subgroup"

-- ==================== Category "Normal" ====================

/-- `g * h * g⁻¹ ∈ N` for normal `N`, `h ∈ N` -/
TheoremDoc Subgroup.Normal.conj_mem as "Normal.conj_mem" in "Normal"

/-- The center `Z(G) = {g | ∀ h, g * h = h * g}` -/
DefinitionDoc Subgroup.center as "Subgroup.center" in "Normal"

/-- `g ∈ Z(G) ↔ ∀ h, g * h = h * g` -/
TheoremDoc Subgroup.mem_center_iff as "Subgroup.mem_center_iff" in "Normal"

/-- The normalizer `N_G(H) = {g | g * H * g⁻¹ = H}` -/
DefinitionDoc Subgroup.normalizer as "Subgroup.normalizer" in "Normal"

/-- `g ∈ N_G(H) ↔ g • H = H` -/
TheoremDoc Subgroup.mem_normalizer_iff as "Subgroup.mem_normalizer_iff" in "Normal"

/-- `N_G(H) = G` iff `H` is normal -/
TheoremDoc Subgroup.normalizer_eq_top as "Subgroup.normalizer_eq_top" in "Normal"

/-- `N_G(H) = ⊤ ↔ H.Normal` -/
TheoremDoc Subgroup.normalizer_eq_top_iff as "Subgroup.normalizer_eq_top_iff" in "Normal"

/-- `H ≤ N_G(H)` -/
TheoremDoc Subgroup.le_normalizer as "Subgroup.le_normalizer" in "Normal"

/-- Every element belongs to `⊤` (the whole group) -/
TheoremDoc Subgroup.mem_top as "Subgroup.mem_top" in "Normal"

-- ==================== Category "Homomorphism" ====================

/-- `φ(a * b) = φ(a) * φ(b)` -/
TheoremDoc map_mul as "map_mul" in "Homomorphism"

/-- `φ(1) = 1` -/
TheoremDoc map_one as "map_one" in "Homomorphism"

/-- `φ(a⁻¹) = φ(a)⁻¹` -/
TheoremDoc map_inv as "map_inv" in "Homomorphism"

/-- Construct a group homomorphism from a mul-preserving function -/
DefinitionDoc MonoidHom.mk' as "MonoidHom.mk'" in "Homomorphism"

/-- `a ∈ ker φ ↔ φ(a) = 1` -/
TheoremDoc MonoidHom.mem_ker as "MonoidHom.mem_ker" in "Homomorphism"

/-- `(ψ ∘ φ)(x) = ψ(φ(x))` as coercion -/
TheoremDoc MonoidHom.coe_comp as "MonoidHom.coe_comp" in "Homomorphism"

/-- Composition of group homomorphisms -/
DefinitionDoc MonoidHom.comp as "MonoidHom.comp" in "Homomorphism"

/-- The identity homomorphism -/
DefinitionDoc MonoidHom.id as "MonoidHom.id" in "Homomorphism"

/-- Construct a `MulEquiv` from maps and inverse proofs -/
DefinitionDoc MulEquiv.intro as "MulEquiv.intro" in "Homomorphism"

/-- `f.symm (f a) = a` for `MulEquiv` -/
TheoremDoc MulEquiv.apply_symm_apply as "MulEquiv.apply_symm_apply" in "Homomorphism"

/-- `f(a * b) = f(a) * f(b)` for `MulEquiv` -/
TheoremDoc MulEquiv.map_mul as "MulEquiv.map_mul" in "Homomorphism"

/-- Introduce a unique existential `∃! x, P x` -/
TheoremDoc ExistsUnique.intro as "ExistsUnique.intro" in "Homomorphism"

/-- `f.LeftInverse g ↔ g ∘ f = id` -/
TheoremDoc Function.leftInverse_iff_comp as "Function.leftInverse_iff_comp" in "Homomorphism"

/-- `f.RightInverse g ↔ f ∘ g = id` -/
TheoremDoc Function.rightInverse_iff_comp as "Function.rightInverse_iff_comp" in "Homomorphism"

/-- `(f ∘ g) x = f (g x)` -/
TheoremDoc Function.comp_apply as "Function.comp_apply" in "Homomorphism"

/-- `(f ∘ g) ∘ h = f ∘ (g ∘ h)` -/
TheoremDoc Function.comp_assoc as "Function.comp_assoc" in "Homomorphism"

-- ==================== Category "GroupAction" ====================

/-- The orbit `G • x = {g • x | g ∈ G}` -/
DefinitionDoc MulAction.orbit as "MulAction.orbit" in "GroupAction"

/-- The stabilizer `Stab(x) = {g | g • x = x}` -/
DefinitionDoc MulAction.stabilizer as "MulAction.stabilizer" in "GroupAction"

/-- `y ∈ orbit G x ↔ ∃ g, g • x = y` -/
TheoremDoc MulAction.mem_orbit as "MulAction.mem_orbit" in "GroupAction"

/-- `g ∈ stabilizer G x ↔ g • x = x` -/
TheoremDoc MulAction.mem_stabilizer_iff as "MulAction.mem_stabilizer_iff" in "GroupAction"

/-- `1 • x = x` -/
TheoremDoc MulAction.one_smul as "MulAction.one_smul" in "GroupAction"

/-- The set of fixed points `{x | ∀ g, g • x = x}` -/
DefinitionDoc MulAction.fixedPoints as "MulAction.fixedPoints" in "GroupAction"

/-- `(g * h) • x = g • (h • x)` -/
TheoremDoc SemigroupAction.mul_smul as "SemigroupAction.mul_smul" in "GroupAction"

/-- `g⁻¹ • (g • x) = x` -/
TheoremDoc inv_smul_smul as "inv_smul_smul" in "GroupAction"

/-- `g • x = y ↔ x = g⁻¹ • y` -/
TheoremDoc smul_eq_iff_eq_inv_smul as "smul_eq_iff_eq_inv_smul" in "GroupAction"

/-- `conj(g)(x) = g * x * g⁻¹` -/
TheoremDoc MulAut.conj_apply as "MulAut.conj_apply" in "GroupAction"

/-- Conjugation action `g • x = g * x * g⁻¹` -/
TheoremDoc MulAut.smul_def as "MulAut.smul_def" in "GroupAction"

/-- `x ∈ g • S ↔ ∃ s ∈ S, g * s * g⁻¹ = x` -/
TheoremDoc Subgroup.mem_smul_pointwise_iff_exists as "Subgroup.mem_smul_pointwise_iff_exists" in "GroupAction"

/-- Fixed points of conjugation = center -/
TheoremDoc ConjAct.fixedPoints_eq_center as "ConjAct.fixedPoints_eq_center" in "GroupAction"

-- ==================== Category "Quotient" ====================

/-- `⟦a⟧ = ⟦b⟧ ↔ a⁻¹ * b ∈ N` in `G ⧸ N` -/
TheoremDoc QuotientGroup.eq as "QuotientGroup.eq" in "Quotient"

/-- `mk'(a) = mk'(b) ↔ a⁻¹ * b ∈ N` -/
TheoremDoc QuotientGroup.mk'_eq_mk' as "QuotientGroup.mk'_eq_mk'" in "Quotient"

/-- `mk(out(x)) = x * n` for some `n ∈ N` -/
TheoremDoc QuotientGroup.mk_out_eq_mul as "QuotientGroup.mk_out_eq_mul" in "Quotient"

/-- The quotient map `G → G ⧸ N` is surjective -/
TheoremDoc QuotientGroup.mk_surjective as "QuotientGroup.mk_surjective" in "Quotient"

-- ==================== Category "PGroup" ====================

/-- A group where every element has p-power order -/
DefinitionDoc IsPGroup as "IsPGroup" in "PGroup"

/-- `|X| ≡ |X^G| (mod p)` for p-group action -/
TheoremDoc IsPGroup.card_modEq_card_fixedPoints as "IsPGroup.card_modEq_card_fixedPoints" in "PGroup"

/-- The center of a nontrivial p-group is nontrivial -/
TheoremDoc IsPGroup.center_nontrivial as "IsPGroup.center_nontrivial" in "PGroup"

/-- If `p ∣ |G|` then `∃ g` with `orderOf g = p` -/
TheoremDoc exists_prime_orderOf_dvd_card as "exists_prime_orderOf_dvd_card" in "PGroup"

/-- The order of an element `g` in a group -/
DefinitionDoc orderOf as "orderOf" in "PGroup"

/-- The cardinality of a finite type -/
DefinitionDoc Fintype.card as "Fintype.card" in "PGroup"

-- ==================== Category "Set" ====================

/-- The type of sets `Set α = α → Prop` -/
DefinitionDoc Set as "Set" in "Set"

/-- `x ∈ {a | p a} ↔ p x` -/
TheoremDoc Set.mem_setOf_eq as "Set.mem_setOf_eq" in "Set"

/-- `x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T` -/
TheoremDoc Set.mem_inter_iff as "Set.mem_inter_iff" in "Set"

/-- `x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T` -/
TheoremDoc Set.mem_union as "Set.mem_union" in "Set"

/-- `x ∈ S * T ↔ ∃ a b, a ∈ S ∧ b ∈ T ∧ a * b = x` -/
TheoremDoc Set.mem_mul_set_iff as "Set.mem_mul_set_iff" in "Set"

/-- `(a, b) ∈ S ×ˢ T ↔ a ∈ S ∧ b ∈ T` -/
TheoremDoc Set.mem_prod as "Set.mem_prod" in "Set"

/-- The range of a function `{f x | x}` -/
DefinitionDoc Set.range as "Set.range" in "Set"

/-- Coerce `SetLike` membership to set membership -/
TheoremDoc SetLike.mem_coe as "SetLike.mem_coe" in "Set"

/-- `P ∨ Q ↔ ¬P → Q` -/
TheoremDoc Classical.or_iff_not_imp_left as "Classical.or_iff_not_imp_left" in "Set"

/-- `P ∨ Q ↔ ¬Q → P` -/
TheoremDoc Classical.or_iff_not_imp_right as "Classical.or_iff_not_imp_right" in "Set"

-- ==================== Category "Equivalence" ====================

/-- `x ≈ x` (reflexivity of equivalence relation) -/
TheoremDoc Setoid.refl as "Setoid.refl" in "Equivalence"

/-- `x ≈ y → y ≈ x` (symmetry) -/
TheoremDoc Setoid.symm as "Setoid.symm" in "Equivalence"

/-- `x ≈ y → y ≈ z → x ≈ z` (transitivity) -/
TheoremDoc Setoid.trans as "Setoid.trans" in "Equivalence"

/-- `[x] = [y] ↔ x ≈ y` -/
TheoremDoc Setoid.equivclass_eq_iff_equiv as "Setoid.equivclass_eq_iff_equiv" in "Equivalence"

/-- Equivalence classes are nonempty -/
TheoremDoc Setoid.equivclass_nonempty as "Setoid.equivclass_nonempty" in "Equivalence"

/-- `x ≈ unquot([x])` -/
TheoremDoc Setoid.unquot_quot_equiv as "Setoid.unquot_quot_equiv" in "Equivalence"

-- ==================== Category "Magma" ====================

/-- `e` is an identity iff `∀ x, e * x = x ∧ x * e = x` -/
DefinitionDoc Mul.isIdentity as "Mul.isIdentity" in "Magma"

/-- `f` preserves multiplication: `f(x * y) = f(x) * f(y)` -/
DefinitionDoc Mul.isMulMap as "Mul.isMulMap" in "Magma"

/-- `f` maps addition to multiplication -/
DefinitionDoc Mul.isAddMulMap as "Mul.isAddMulMap" in "Magma"

/-- A set is a magma if closed under multiplication -/
DefinitionDoc Set.isMagma as "Set.isMagma" in "Magma"

/-- A set is an additive magma if closed under addition -/
DefinitionDoc Set.isAddMagma as "Set.isAddMagma" in "Magma"

/-- Construct a proof that a type is empty -/
DefinitionDoc IsEmpty.mk as "IsEmpty.mk" in "Magma"

/-- `0 ≤ x ^ 2` for any `x` -/
TheoremDoc sq_nonneg as "sq_nonneg" in "Magma"

/-- `x ^ 2 = x * x` -/
TheoremDoc pow_two as "pow_two" in "Magma"

/-- `(x ^ (1/n)) ^ n = x` for complex numbers -/
TheoremDoc Complex.cpow_nat_inv_pow as "Complex.cpow_nat_inv_pow" in "Magma"

/-- `exp(a + b) = exp(a) * exp(b)` -/
TheoremDoc Real.exp_add as "Real.exp_add" in "Magma"

-- ==================== Category "Nat" ====================

/-- `(a * b) * c = a * (b * c)` for natural numbers -/
TheoremDoc Nat.mul_assoc as "Nat.mul_assoc" in "Nat"

/-- `a * b = b * a` for natural numbers -/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Nat"

/-- `a + b = b + a` for natural numbers -/
TheoremDoc Nat.add_comm as "Nat.add_comm" in "Nat"

/-- `(a % n + b) % n = (a + b) % n` -/
TheoremDoc Nat.mod_add_mod as "Nat.mod_add_mod" in "Nat"

/-- `(a + b % n) % n = (a + b) % n` -/
TheoremDoc Nat.add_mod_mod as "Nat.add_mod_mod" in "Nat"

/-- `a < n → a % n = a` -/
TheoremDoc Nat.mod_eq_of_lt as "Nat.mod_eq_of_lt" in "Nat"

/-- `n % n = 0` -/
TheoremDoc Nat.mod_self as "Nat.mod_self" in "Nat"

/-- `a % (n+1) = a ↔ a < n+1` -/
TheoremDoc Nat.mod_succ_eq_iff_lt as "Nat.mod_succ_eq_iff_lt" in "Nat"

/-- `a < b → b ≠ 0` -/
TheoremDoc Nat.ne_zero_of_lt as "Nat.ne_zero_of_lt" in "Nat"

/-- `n ≤ m → m - n + n = m` -/
TheoremDoc Nat.sub_add_cancel as "Nat.sub_add_cancel" in "Nat"

/-- `∀ a, a ∣ 0` -/
TheoremDoc dvd_zero as "dvd_zero" in "Nat"

/-- `a ∣ b ↔ a ∣ -b` -/
TheoremDoc dvd_neg as "dvd_neg" in "Nat"

/-- `a ∣ b → a ∣ c → a ∣ b + c` -/
TheoremDoc dvd_add as "dvd_add" in "Nat"

/-- `a - a = 0` -/
TheoremDoc sub_self as "sub_self" in "Nat"

/-- `-(a - b) = b - a` -/
TheoremDoc neg_sub as "neg_sub" in "Nat"

/-- `a - b + (b - c) = a - c` -/
TheoremDoc sub_add_sub_cancel as "sub_add_sub_cancel" in "Nat"

/-- `(a - b) % n = (a % n - b % n) % n` -/
TheoremDoc Int.sub_emod as "Int.sub_emod" in "Nat"

-- ==================== Category "Fin" ====================

/-- `i.val < n` for `i : Fin n` -/
TheoremDoc Fin.is_lt as "Fin.is_lt" in "Fin"

/-- `i.val ≤ n - 1` for `i : Fin n` -/
TheoremDoc Fin.is_le' as "Fin.is_le'" in "Fin"

/-- `Fin.mk a ha = Fin.mk b hb ↔ a = b` -/
TheoremDoc Fin.mk.injEq as "Fin.mk.injEq" in "Fin"

/-- `(0 : Fin n) = ⟨0, _⟩` -/
TheoremDoc Fin.zero_eta as "Fin.zero_eta" in "Fin"

/-- Extensionality: equal components imply equal terms -/
TheoremDoc ext_lemma as "ext_lemma" in "Fin"

/-- Construct a commutative group from operations and proofs -/
DefinitionDoc CommGroup_mk as "CommGroup_mk" in "Fin"

-- ==================== Category "Custom" ====================

/-- Unfold `SubSetP` membership definition -/
DefinitionDoc SubSetP.def as "SubSetP.def" in "Custom"

/-- Construct an additive subgroup class -/
DefinitionDoc addsubgroupclass_make as "addsubgroupclass_make" in "Custom"

/-- Construct an equiv from a bijective function -/
DefinitionDoc Equiv.ofBijective as "Equiv.ofBijective" in "Custom"

/-- Addition operation -/
DefinitionDoc add as "add" in "Custom"

/-- Negation operation -/
DefinitionDoc neg as "neg" in "Custom"

/-- The zero element -/
DefinitionDoc zero as "zero" in "Custom"

/-- The quotient map sending `x` to its equivalence class -/
DefinitionDoc Setoid.quot as "Setoid.quot" in "Custom"

--lemma have_intro {Q : Prop} (P : Prop) (p : P) : (P→Q) → Q  := fun h => h p
