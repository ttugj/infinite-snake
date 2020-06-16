import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor

class invol (α : Type) := (invol : α → α) (invol_eq : invol ∘ invol = id)

class ambient_module (k : Type) (M : Type) 
[comm_ring k] [lie_ring M] [lie_algebra k M] :=
-- sl2 with half-H 
(E : M) (H : M) (F : M)
-- circle 
(z : ℤ → (module.End k M)) 
-- shift
(σ : lie_algebra.morphism k M M)
-- involution 
(τ : lie_algebra.morphism k M M)
-- structure
(str_sl2 : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = 2 • H ∧ ⁅H, F⁆ = -F)
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
                ⁅(z i) E, (z j) m⁆ = j • (z (i+j+1)) m + (z j) ⁅(z i) E, m⁆ 
              ∧ ⁅(z i) H, (z j) m⁆ = j • (z (i+j  )) m + (z j) ⁅(z i) H, m⁆ 
              ∧ ⁅(z i) F, (z j) m⁆ = j • (z (i+j-1)) m + (z j) ⁅(z i) F, m⁆)

namespace ambient_module

variables (k : Type) [comm_ring k]

instance ambient_invol {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] : invol M :=
⟨@τ k _ _ _ _ _, @str_invol k _ _ _ _ _⟩ 

def is_serpentine 
{M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M]  -- lots of instances here...
(ζ : M) : Prop :=
(ζ = E k + (@z k _ _ _ _ _ 1) (@σ k _ _ _ _ _ (ζ - H k))) 

end ambient_module

inductive gen | A : gen | A' : gen
def words := free_semigroup gen

namespace gen

def τ : gen → gen | A := A'| A' := A

def τ_eq : τ ∘ τ = id :=
begin rw function.comp, funext, cases x, unfold τ, simp, unfold τ, simp, end

instance : invol gen := ⟨τ, τ_eq⟩

end gen


namespace words 

instance : invol words := ⟨functor.map gen.τ, begin rw functor.map_comp_map, rw ←functor.map_id, rw gen.τ_eq, end⟩

instance [c : semigroup (free_semigroup gen)] : semigroup words := begin unfold words, exact c end

def of (a : gen) : words := free_semigroup.of a 

-- simple recursor
def rec {α : Type} (ze : gen → α) (su : gen → α → α) (w : words) : α :=
prod.fst $ @free_semigroup.rec_on gen 
                (λ _,  (α × gen)) w 
                (λ (a : gen), (ze a, a)) 
                (λ (_ : gen) (_ : words) (a b : α × gen), (su a.2 b.1, a.2))
               

 
lemma rec_ze { α : Type } : ∀ (ze : gen → α) (su : gen → α → α) (a : gen),
                            rec ze su (of a) = ze a
:= sorry

lemma rec_su { α : Type } : ∀ (ze : gen → α) (su : gen → α → α) (w : words) (a : gen),
                            rec ze su (of a * w) = su a (rec ze su w)
:= sorry

-- state and prove defining properties...

end words

namespace ambient_module

-- def interpret {M : Type} [ambient_module k M] (ζ : M) (w : words) : M :=   

end ambient_module
