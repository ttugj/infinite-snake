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

def su_A (hζ : serpentine ζ) : ∀ (b : words), rel' ζ b → rel' ζ (words.of gen.A * b)
:= begin
    sorry
end

def su_A' (hζ : serpentine ζ) : ∀ (b : words), rel' ζ b → rel' ζ (words.of gen.A' * b)
:= begin
    intros,
    have h := rel_invol (su_A hζ (invol.invol b) (rel_invol a)),
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
    exact (su_A  hζ b a_2),
    exact (su_A' hζ b a_2)
end


/-
:= begin
    intros, unfold rel', unfold rel' at a_2, unfold rel' at a_1, 
    simp [words.wt_su], simp [words.μ_su], simp [interpret_su], simp [interpret_sl2_su], simp [phrases.R_su],
    simp [interpret_ze, words.wt_ze, phrases.R_ze, words.μ_ze, interpret_sl2_ze] at a_1,
    conv_lhs { rw a_1, rw a_2 }, 
    -- first deal with brackets
    rw lie_add, rw add_lie, rw add_lie,
    have h1 : ∀ (i : int) (x : M), ⁅ interpret_sl2_gen a, z i (σ x) ⁆ = (words.wt_gen a * i) • z (words.wt_gen a + i) (σ x) := by admit, -- TODO
    have h2 : ∀ (i j : int) (x y : M),  ⁅ z i (σ x), z j (σ y) ⁆ = z (i+j) (σ ⁅x,y⁆) := by admit, -- TODO
    simp [h1,h2],
    simp [serpentine.interpret_wt hζ],
    simp [interpret_phrase_ω hζ],
    simp [interpret_phrase_α ζ],
    have h3: /-∀ (a : gen),-/ ⁅ interpret_gen ζ a, H ⁆ = -(words.wt_gen a) • interpret_gen ζ a := by admit, -- TODO
    have h4: ∀ /-(b : words)-/ (i : int) (x : M), ⁅ z i (σ x), interpret_sl2 b ⁆ = -b.μ • z (b.wt + i) (σ x) := by admit, -- TODO
    simp [h3,h4],
    rw ←interpret_su,
    erw ←interpret_sl2_su, 
    -- no brackets left at this point
    unfold phrases.R_su_fun,
    conv_lhs { rw add_assoc }, congr,
    -- both sides are z _ (σ _): rhs explicitly, lhs implicitly 
    -- now we massage lhs into desired form
    have h5: ∀ (c : int) (x : M), -(c • x) = (-c) • x := begin intros, rw ←(neg_smul c x) end,
    have h6: ∀ (c i : int) (x : M), c • z i x = z i (c • x) := begin intros, rw ←(linear_map.map_smul (z i) c x) end, 
    have h7: ∀ (i : int) (x y : M), z i x + z i y = z i (x + y) := begin intros, rw ←(linear_map.map_add (z i) x y) end,
    repeat { rw (add_comm b.wt (words.wt_gen a)) }, 
    repeat { rw h5 }, 
    repeat { rw h6 },
    repeat { rw h7 },
    congr' 1, -- kill z
    have h8: ∀ (c : int) (x : M), c • σ x = σ (c • x) := by admit, -- TODO
    have h9: ∀ (x y : M), σ x + σ y = σ (x + y) := begin intros, symmetry, exact (linear_map.map_add σ.to_linear_map x y) end,
    repeat { rw h8 },
    repeat { rw h9 },
    congr' 1, -- kill σ
    -- it should be easy from now on
    simp [ interpret_phrase_δ ζ, interpret_ze ζ ],
    simp [ sub_eq_add_neg, smul_add ],
    repeat { rw (interpret_phrase_add ζ) },
    repeat { rw (interpret_phrase_smul ζ) },
    repeat { rw smul_smul },
    simp [ ←mul_assoc, ←add_assoc, ←neg_smul ],
end
-/

theorem rel (hζ : serpentine ζ) : ∀ (w : words), rel' ζ w :=
begin
    intros, exact (free_semigroup.rec_on w (ze hζ) (su hζ))
end

end rec_rel

end ambient_module

-- ⁅    ⁆
