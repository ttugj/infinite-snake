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

noncomputable theory

namespace words

/-- free `R`-module over `words` -/
def mod (R : Type) [ring R] := words →₀ R 

namespace mod

variables {R : Type} [ring R]

instance : add_comm_group (mod R) := @finsupp.add_comm_group words R _
instance : module R (mod R) := @finsupp.module words R _ _ _ _

def univ {A : Type} [add_comm_group A] [module R A] (φ : words → A) : mod R →ₗ[R] A 
:= finsupp.total words A R φ

def τ : module.End R (mod R) := finsupp.lmap_domain R R invol.invol

def τ_eq : linear_map.comp τ τ = (linear_map.id : module.End R (mod R))
:= begin unfold τ, rw ←finsupp.lmap_domain_comp, rw invol.invol_eq, rw finsupp.lmap_domain_id end

instance : invol (mod R) := 
⟨τ, begin 
    funext, intros, have h := τ_eq, rw linear_map.ext_iff at h, have h' := h x,
    rw linear_map.comp_apply at h', rw function.comp_apply, exact h' 
end⟩

end mod

end words

/-- free abelian group over `words` -/
def phrases := words.mod ℤ 

namespace phrases

instance : add_comm_group phrases := words.mod.add_comm_group
instance : module ℤ phrases := words.mod.module 
instance : invol phrases := words.mod.invol

def univ {A : Type} [add_comm_group A] [module ℤ A] (φ : words → A) : phrases →ₗ[ℤ] A := words.mod.univ φ

def δ (c : ℤ) (w : words) : phrases := finsupp.single w c

lemma δ_invol (c : int) (w : words) : invol.invol (δ c w) = δ c (invol.invol w) := by sorry -- TODO

def ω : module.End ℤ phrases := univ (λ w, δ w.wt w) 

lemma ω_invol : ∀ (r : phrases), invol.invol (ω r) = - (ω (invol.invol r)) := by sorry -- TODO

-- left action of words (as a monoid) on phrases (as an abelian group)
def α (w : words) : module.End ℤ phrases := univ (λ w', δ 1 (w * w')) 

lemma α_invol (w : words) : ∀ (r : phrases), invol.invol (α w r) = α (invol.invol w) (invol.invol r) := by sorry -- TODO

def R_su_fun (a : gen) (b : words) (r : phrases) :=
α (words.of a) r + words.wt_gen a • (b.wt • r + ω r + δ (2 * b.wt) b - δ (2 * b.μ) (words.of a)) 

def R : words → phrases := words.rec (λ _, 0) R_su_fun

lemma R_ze (a : gen) : R (words.of a) = 0 := begin
    intros,  unfold R, simp [words.rec_ze]  
end

lemma R_su (a : gen) (b : words) : R (words.of a * b) = R_su_fun a b (R b) 
:= begin
    intros, unfold R, simp [words.rec_su]
end

namespace R_invol

def claim (w : words) := R (invol.invol w) = invol.invol (R w)

def ze (a : gen) : claim (words.of a) := begin
    intros, unfold claim, rw words.invol_of, simp [R_ze], unfold invol.invol, simp [linear_map.map_zero] 
end

def su (a : gen) (b : words) : claim (words.of a) → claim b → claim (words.of a * b) := begin
    intros, unfold claim, 
    have h : ∀ (w w' : words), invol.invol (w * w') = invol.invol w * invol.invol w' := by sorry, -- TODO
    rw h,
    rw R_su, unfold R_su_fun,
    have h1 : ∀ (r s : phrases), invol.invol (r + s) = invol.invol r + invol.invol s := by sorry, -- TODO
    have h2 : ∀ (r s : phrases), invol.invol (r - s) = invol.invol r - invol.invol s := by sorry, -- TODO
    have h3 : ∀ (c : int) (r : phrases), invol.invol (c • r) = c • invol.invol r := by sorry, -- TODO
    repeat { rw [ h1, h3, h2 ] },
    rw h1, rw h1, rw h3,
    repeat { rw [ α_invol, δ_invol, ω_invol ] }, erw δ_invol,
    rw words.invol_of,
    rw R_su, unfold R_su_fun,
    unfold claim at a_2,
    rw a_2,
    rw words.wt_gen_invol,
    rw words.wt_invol,
    rw words.μ_invol,
    simp [neg_smul, smul_neg, smul_add, smul_sub, smul_smul],
    have h4 : ∀ (c : int) (w : words), δ (-c) w = -(δ c w) := by sorry, -- TODO
    repeat { rw h4 },
    simp [smul_neg, sub_eq_add_neg ]
end

end R_invol

lemma R_invol : ∀ (w : words), R (invol.invol w) = invol.invol (R w)
:= begin
    intros, exact (free_semigroup.rec_on w R_invol.ze R_invol.su) 
end

end phrases

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

def interpret_phrase (ζ : M) : phrases →ₗ[ℤ] M := phrases.univ (interpret ζ) 
def interpret_sl2_phrase : phrases →ₗ[ℤ] M := phrases.univ interpret_sl2 

lemma interpret_phrase_ω {ζ : M} (hζ : serpentine ζ) : ∀ (r : phrases), ⁅ H,  interpret_phrase ζ r ⁆ = interpret_phrase ζ r.ω
:= by sorry -- TODO

lemma interpret_phrase_α (ζ : M) : ∀ (a : gen) (r : phrases), ⁅ interpret_gen ζ a,  interpret_phrase ζ r ⁆ = interpret_phrase ζ (phrases.α (words.of a) r)
:= by sorry -- TODO

lemma interpret_phrase_δ (ζ : M) : ∀ (c : int) (w : words), interpret_phrase ζ (phrases.δ c w) = c • interpret ζ w
:= by sorry -- TODO

lemma interpret_phrase_add (ζ : M) : ∀  (r r' : phrases), interpret_phrase ζ (r + r') = interpret_phrase ζ r + interpret_phrase ζ r'
:= by sorry -- TODO

lemma interpret_phrase_sub (ζ : M) : ∀ (r r' : phrases), interpret_phrase ζ (r - r') = interpret_phrase ζ r - interpret_phrase ζ r'
:= by sorry -- TODO

lemma interpret_phrase_smul (ζ : M) : ∀ (c : int) (r : phrases), interpret_phrase ζ (c • r) = c • interpret_phrase ζ r
:= by sorry -- TODO


namespace rec_rel

def rel' (ζ : M) (w : words) : Prop 
:= interpret ζ w = interpret_sl2 w + (z w.wt ∘ σ) (interpret ζ w + w.μ • H + interpret_phrase ζ (phrases.R w)) 

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
    
def su (hζ : serpentine ζ) : ∀ (a : gen) (b : words), rel' ζ (words.of a) → rel' ζ b → rel' ζ (words.of a * b) 
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
    have h9: ∀ (x y : M), σ x + σ y = σ (x + y) := by admit, -- TODO
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
    cases a,
    -- case A
    unfold words.wt_gen, unfold interpret_gen, simp [mul_one,one_mul,one_smul], admit, -- TODO / for now
    -- case A'
    unfold words.wt_gen, unfold interpret_gen, simp [mul_one,one_mul,one_smul], abel
end

theorem rel (hζ : serpentine ζ) : ∀ (w : words), rel' ζ w :=
begin
    intros, exact (free_semigroup.rec_on w (ze hζ) (su hζ))
end

end rec_rel

end ambient_module

-- ⁅    ⁆
