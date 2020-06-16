import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor

universe u

class invol (α : Type u) := (invol : α → α) (invol_eq : invol ∘ invol = id)

section over_k

variables (k : Type u) [comm_ring k]

class ambient_module (M : Type u) 
[lie_ring M] [lie_algebra k M] :=
-- sl2
(E : M) (H : M) (F : M)
-- circle 
(z : ℤ → (module.End k M)) 
-- shift
(σ : lie_algebra.morphism k M M)
-- involution 
(τ : lie_algebra.morphism k M M)
-- structure
(str_sl2 : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = H ∧ ⁅F, H⁆ = F)
(str_circle : z 0 = linear_map.id ∧ ∀ (i j : ℤ), z i ∘ z j = z (i + j))
(str_invol : τ ∘ τ = id)
(invol_sl2 : τ E = -F ∧ τ H = -H ∧ τ F = -E)
(invol_circle : ∀ (i : ℤ), τ ∘ (z i) = z (-i))
(invol_shift : τ ∘ σ = σ ∘ τ)
(sl2_shift : ∀ (m : M) (i j : ℤ), 
               ⁅(z i) E, (z j) (σ m)⁆ = 0
             ∧ ⁅(z i) H, (z j) (σ m)⁆ = 0 
             ∧ ⁅(z i) F, (z j) (σ m)⁆ = 0)
(circle_shift : ∀ (m m' : M) (i j : ℤ), ⁅(z i) m, (z j) (σ m')⁆ = (z i) ⁅m, (z j) (σ m')⁆)
(sl2_circle : ∀ (i j : ℤ) (m : M), 
                ⁅(z i) E, (z j) m⁆ =     j • (z (i+j+1)) m + (z j) ⁅(z i) E, m⁆ 
              ∧ ⁅(z i) H, (z j) m⁆ = (2*j) • (z (i+j  )) m + (z j) ⁅(z i) H, m⁆ 
              ∧ ⁅(z i) F, (z j) m⁆ =     j • (z (i+j-1)) m + (z j) ⁅(z i) F, m⁆)

instance ambient_invol {M : Type u} [lie_ring M] [lie_algebra k M] [ambient_module k M] : invol M :=
⟨@ambient_module.τ k _ M _ _ _, ambient_module.str_invol⟩

end over_k

namespace ambient_module

end ambient_module

inductive gen | A : gen | A' : gen
def words := free_semigroup gen

namespace gen

def τ : gen → gen | A := A'| A' := A

def τ_eq : τ ∘ τ = id :=
begin rw function.comp, funext, cases x, unfold τ, simp, unfold τ, simp, end

instance : invol gen := ⟨τ, τ_eq⟩

end gen

instance : invol words := ⟨functor.map gen.τ, begin rw functor.map_comp_map, rw ←functor.map_id, rw gen.τ_eq, end⟩


