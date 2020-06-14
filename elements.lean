import algebra.ring
import algebra.module
import algebra.lie_algebra
import algebra.classical_lie_algebras
import ring_theory.algebra
import data.matrix.basic

universe u

class has_invol (α : Type u) := (invol : α → α) (invol_eq : invol ∘ invol = id)

def τ {α : Type u} [has_invol α] := @has_invol.invol α

class invol_add_comm_group (A : Type u) [add_comm_group A] extends has_invol A :=
(invol_add   : ∀ (a b : A), τ (a + b) = τ a + τ b)
(invol_zero  : τ (0 : A) = (0 : A))
(invol_neg   : ∀ (a : A), τ (-a) = -(τ a))

class invol_lie_ring (L : Type u) [lie_ring L]  extends invol_add_comm_group L :=
(invol_bracket : ∀ (x y : L), ⁅τ x, τ y⁆ = ⁅x, y⁆)

class invol_comm_ring (R : Type u) [comm_ring R] extends invol_add_comm_group R :=
(invol_mul : ∀ (r s : R), τ (r * s) = τ r * τ s)
(invol_one : τ (1 : R) = (1 : R)) 

class invol_module_over_invol_ring (R: Type u) (M : Type u) 
[comm_ring R] [invol_comm_ring R] 
[add_comm_group M] [module R M] extends invol_add_comm_group M :=
(invol_module  : ∀ (r : R) (m : M),  τ (r • m) = (τ r) • (τ m))  

variables (k : Type u) [comm_ring k]

class invol_module (M : Type u) [add_comm_group M] [module k M] extends invol_add_comm_group M :=
(invol_module  : ∀ (c : k) (m : M),  τ (c • m) = c • (τ m))  

-- model: (special_linear.sl 2 k), with ...
class is_sl2 (L : Type u) 
[lie_ring L] [lie_algebra k L]
[invol_lie_ring L] [invol_module k L]
:=
(E : L) (H : L) (F : L)
(str_eq : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = H ∧ ⁅F, H⁆ = F)
(invol_sl2 : τ E = -F ∧ τ H = -H ∧ τ F = -E)
(univ : Π {M : Type u} [add_comm_group M] [module k M] (e h f : M), L →+ M)
(univ_eq : ∀ {M : Type u} [add_comm_group M] [module k M] (e h f : M), univ e h f E = e ∧ univ e h f H = h ∧ univ e h f F = f)

namespace models

open lie_algebra

def sl2 := coe_sort (special_linear.sl (fin 2) k)

def invol_sl2_closed (A : sl2 k) : matrix.trace (fin 2) k k (-A.val.transpose) = 0 := begin
    rw (by simp : matrix.trace (fin 2) k k (-A.val.transpose) = -(matrix.trace (fin 2) k k A.val)),
    rw (set.mem_def.1 A.property : matrix.trace (fin 2) k k A.val = 0),
    simp,
end

instance : has_invol (sl2 k) := {
    invol := λ A, ⟨-A.val.transpose, invol_sl2_closed k A⟩,
    invol_eq := begin rw function.comp, simp, refl end
}

end models

class is_circle (R : Type u) 
[comm_ring R] [algebra k R] 
[invol_add_comm_group R] [invol_module k R]
:=
(z : ℤ → R) 
(str_eq : z 0 = comm_ring.one ∧ ∀ (i j : ℤ), z i * z j = z (i + j))
(univ : Π  {M : Type u} [add_comm_group M] [module k M] (w : ℤ → M), R →+ M)
(univ_eq : ∀ {M : Type u} [add_comm_group M] [module k M] (w : ℤ → M), univ w ∘ z = w) 
(invol_z : ∀ (i : ℤ), τ (z i) = z (-i)) 

namespace models

def circle := add_monoid_algebra k ℤ 

end models

def sl2_circle_action (R : Type u) (L : Type u)
[comm_ring R] [algebra k R] 
[invol_add_comm_group R] [invol_module k R]
[is_circle k R]
[lie_ring L] [lie_algebra k L]
[invol_lie_ring L] [invol_module k L]
[is_sl2 k L]
[module k (R →+ R)] -- hmm...
: L → (R →+ R)
:=
let (e' : R →+ R) := is_circle.univ k $ λ (i : ℤ), i • (is_circle.z k (i+1) : R),
    (h' : R →+ R) := is_circle.univ k $ λ (i : ℤ), 2 * i • (is_circle.z k i : R), 
    (f' : R →+ R) := is_circle.univ k $ λ (i : ℤ), i • (is_circle.z k (i-1) : R) 
in is_sl2.univ k e' h' f' 

