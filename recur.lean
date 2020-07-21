import algebra.lie_algebra
import algebra.module
import data.finsupp
import linear_algebra.finsupp

import .words
import .ambient

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

def univ {A : Type} [add_comm_group A] [module ℤ A] (φ : words → A) : phrases →ₗ[ℤ] A := words.mod.univ φ

def δ (c : ℤ) (w : words) : phrases := finsupp.single w c

def ω : module.End ℤ phrases := univ (λ w, δ w.wt w) 

def α (w : words) : module.End ℤ phrases := univ (λ w', δ 1 (w * w')) 

def R_su (a : gen) (b : words) (r : phrases) :=
α (words.of a) r - words.wt_gen a • (b.wt • r + ω r + δ (2 * b.wt) b - δ (2 * b.μ) (words.of a)) 

def R : words → phrases := words.rec (λ _, 0) R_su

end phrases

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

def interpret_phrase (ζ : M) : phrases →ₗ[ℤ] M := phrases.univ (interpret ζ) 
def interpret_sl2_phrase : phrases →ₗ[ℤ] M := phrases.univ interpret_sl2 

/- basic instance of the recurrence relation -/
def rec_rel' (ζ : M) (w : words) : Prop 
:= interpret ζ w - (neg_z w.wt ∘ σ) (interpret ζ w) - interpret_sl2 w 
 = (neg_z w.wt ∘ σ) (interpret_phrase ζ (phrases.R w) - w.μ • H) 

theorem rec_rel {ζ : M} (hζ : serpentine ζ) : ∀ (w : words), rec_rel' ζ w :=
begin
    have hz : ∀ (a : gen), rec_rel' ζ (words.of a) := by sorry,
    have hs : ∀ (a : gen) (b : words), rec_rel' ζ (words.of a) → rec_rel' ζ b → rec_rel' ζ (words.of a * b) := by sorry,
    intros,
    exact (free_semigroup.rec_on w hz hs)
end

end ambient_module
