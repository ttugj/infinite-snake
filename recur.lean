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

end mod

end words

/-- free abelian group over `words` -/
def phrases := words.mod ℤ 

namespace phrases

instance : add_comm_group phrases := words.mod.add_comm_group
instance : module ℤ phrases := words.mod.module 

def univ {A : Type} [add_comm_group A] [module ℤ A] (φ : words → A) : phrases →ₗ[ℤ] A := words.mod.univ φ

def δ (c : ℤ) (w : words) : phrases := finsupp.single w c

lemma univ_id : univ (δ 1) = linear_map.id
:= begin
    sorry
end

lemma univ_comp {A : Type} [add_comm_group A] [module ℤ A] :
      ∀ (φ : words → A) (g : words → words), univ φ ∘ univ (δ 1 ∘ g) = univ (φ ∘ g)
:= begin
    sorry 
end

def ω : module.End ℤ phrases := univ (λ w, δ w.wt w) 

def α (w : words) : module.End ℤ phrases := univ (λ w', δ 1 (w * w')) 

def τ : module.End ℤ phrases := univ (δ 1 ∘ invol.invol) 

def τ_eq : τ ∘ τ = id := 
begin
    unfold τ, simp [univ_comp], rw function.comp.assoc, rw invol.invol_eq, rw function.right_id, 
    simp [univ_id], refl 
end

def R_su (a : gen) (b : words) (r : phrases) :=
α (words.of a) r - words.wt_gen a • (b.wt • r + ω r + δ (2 * b.wt) b - δ (2 * b.μ) (words.of a)) 

def R : words → phrases := words.rec (λ _, 0) R_su


end phrases

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

def interpret_phrase (ζ : M) : phrases →ₗ[ℤ] M := phrases.univ (interpret ζ) 
def interpret_sl2_phrase : phrases →ₗ[ℤ] M := phrases.univ interpret_sl2 

end ambient_module
