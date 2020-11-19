/- General recurrence relations in ambient modules. 
   Main theorem: rec_rel.rel.
-/

import algebra.lie_algebra
import algebra.module
import data.finsupp
import linear_algebra.finsupp

import .words
import .ambient
import .base
import .phrases

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

namespace rec_rel

def rel' (ζ : M) (w : words) : Prop 
:= interpret ζ w = interpret_sl2 w + (z w.wt ∘ σ) (interpret ζ w + w.μ • H + interpret_phrase ζ (phrases.R w)) 

lemma rel_invol {ζ : M} {w : words} : rel' ζ w → rel' ζ (invol.invol w) :=
begin
    intros, unfold rel' at a, unfold rel',
    rw interpret_invol,
    rw interpret_sl2_invol,
    rw words.μ_invol,
    rw words.wt_invol,
    rw phrases.R_invol,
    rw interpret_phrase_invol,
    conv_lhs { rw a },
    unfold invol.invol,
    have h1 : ∀ (x y : M), τ (x + y) = τ x + τ y := linear_map.map_add τ.to_linear_map,
    have h2 : ∀ (i : int) (x : M), τ (z i x) = z (-i) (τ x) := by sorry, -- TODO
    have h3 : ∀ (x : M), τ (σ x) = σ (τ x) := by sorry, -- TODO
    have h4 : ∀ (c : int), τ (c • H) = -(c • H : M) := by sorry, -- TODO
    simp [h1,h2,h3,h4]
end 

variables {ζ : M} 

def ze (hζ : serpentine ζ) : ∀ (a : gen), rel' ζ (words.of a) 
:= begin
            intros, unfold rel', simp [words.wt_ze], simp [phrases.R_ze], simp [interpret_ze], cases a,
            unfold serpentine at hζ,
            -- case A
            simp [words.μ_ze], simp [interpret_sl2_ze],  unfold interpret_gen, unfold words.wt_gen, unfold interpret_sl2_gen,
            conv_lhs { rw hζ }, simp, 
            -- case A'
            simp [words.μ_ze], simp [interpret_sl2_ze],  unfold interpret_gen, unfold words.wt_gen, unfold interpret_sl2_gen,
            conv_lhs { rw (serpentine.invol hζ) }, simp, erw (sub_eq_add_neg (τ ζ) H)
end

def su_A (hζ : serpentine ζ) {b : words} : rel' ζ b → rel' ζ (words.of gen.A * b)
:= begin
    intros, unfold rel', unfold rel' at a,
    simp [words.wt_su], simp [words.μ_su], simp [interpret_su], simp [interpret_sl2_su], simp [phrases.R_su],
    unfold interpret_gen, unfold interpret_sl2_gen,
    have hζ' := hζ, unfold serpentine at hζ', conv_lhs { congr, rw hζ' }, conv_lhs { rw a },
    repeat { rw [lie_add, add_lie] },
    have h1 : ∀ (i : int) (x : M), ⁅ E, z i (σ x) ⁆ = i • z (i+1) (σ x) := by admit, -- TODO
    have h2 : ∀ (i j : int) (x y : M),  ⁅ z i (σ x), z j (σ y) ⁆ = z (i+j) (σ ⁅x,y⁆) := by admit, -- TODO
    simp [h1, h2],
    unfold words.wt_gen,
    simp [serpentine.interpret_wt hζ],
    simp [interpret_phrase_ω hζ],
    have hα := interpret_phrase_α ζ (gen.A), unfold interpret_gen at hα, simp [hα],
    rw ←(lie_skew ζ H), rw (serpentine.act_H hζ),
    have hμ := interpret_sl2_μ b 1 (σ (ζ + H : M)), unfold Φ at hμ, rw ←lie_skew at hμ,
    have h3 : ∀ (x y z : M), -x-y=z → x=-y-z := begin intros, rw ←a_1, abel end,
    simp [h3 _ _ _ hμ],
    have h4 : ∀ (x : M), ⁅interpret_sl2 b, σ x⁆ = 0 := by sorry, -- TODO
    simp [h4],
    unfold phrases.R_su_fun,
    unfold words.wt_gen,
    conv_lhs { rw add_assoc }, congr, -- kill initial term
    have h5: ∀ (c : int) (x : M), -(c • x) = (-c) • x := begin intros, rw ←(neg_smul c x) end,
    have h6: ∀ (c i : int) (x : M), c • z i x = z i (c • x) := begin intros, rw ←(linear_map.map_smul (z i) c x) end, 
    have h7: ∀ (i : int) (x y : M), z i x + z i y = z i (x + y) := begin intros, rw ←(linear_map.map_add (z i) x y) end,
    repeat { rw (add_comm b.wt 1) }, 
    repeat { rw h5 }, 
    repeat { rw h6 },
    repeat { rw h7 },
    congr' 1, -- kill z
    have h8: ∀ (c : int) (x : M), c • σ x = σ (c • x) := by sorry, -- TODO (?!!)
    have h9: ∀ (x y : M), σ x + σ y = σ (x + y) := begin intros, symmetry, exact (linear_map.map_add σ.to_linear_map x y) end,
    repeat { rw h8 },
    repeat { rw h9 },
    congr' 1, -- kill σ
    repeat { rw smul_add },
    erw smul_sub,
    erw sub_mul,
    repeat { rw ←add_assoc },
    erw sub_smul,
    repeat { rw smul_add },
    erw add_sub,
    repeat { erw ←add_assoc },  
    simp [one_smul, mul_smul],
    simp [interpret_phrase_δ, interpret_ze, interpret_gen],
    repeat { erw ←mul_smul },
    repeat { erw ←neg_smul },
    -- pretty much ready, now just some massaging
    have h10 : ∀ (a1 a1' a2 a2' a3 a3' a4 a5 a6 a7 : M), a1 + a2 + a3 + a2' + a4 + a5 + a3' + a1' + a6 + a7 = 
                                                         a5 + a2' - (-a2) + a6 + a4 + a7 + (a3 + a3') + (a1 + a1') :=
                                                         begin intros, abel end,
    conv_lhs { rw h10 }, simp,
    have h11 : ∀ (c : int) (x : M), c • x + c • x = (2 * c) • x := begin intros, rw ←add_smul, congr, conv_lhs { rw ←(one_mul c), rw ←add_mul }, congr end, 
    have h12 : ∀ (c : int) (x : M), -(c • x) + -(c • x) = -((2 * c) • x) := begin intros, rw ←neg_smul, rw h11, rw ←neg_mul_eq_mul_neg, rw neg_smul end,
    conv_lhs { rw h11, rw h12 }, 
    abel -- overkill, just need to reassociate
end

def su_A' (hζ : serpentine ζ) {b : words} : rel' ζ b → rel' ζ (words.of gen.A' * b)
:= begin
    intros,
    have h := rel_invol (su_A hζ (rel_invol a)),
    rw words.invol_mul at h,
    rw words.invol_of at h,
    unfold gen.τ at h,
    rw ←(function.comp_app invol.invol invol.invol b) at h,
    rw invol.invol_eq at h,
    unfold id at h, 
    exact h
end

def su (hζ : serpentine ζ) : ∀ (a : gen) (b : words), rel' ζ (words.of a) → rel' ζ b → rel' ζ (words.of a * b) 
:= begin
    intros, cases a,
    exact (su_A  hζ a_2),
    exact (su_A' hζ a_2)
end

theorem rel (hζ : serpentine ζ) : ∀ (w : words), rel' ζ w :=
begin
    intros, exact (free_semigroup.rec_on w (ze hζ) (su hζ))
end

end rec_rel

end ambient_module

-- ⁅    ⁆
