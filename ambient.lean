import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor
import tactic

import .words

class ambient_module (M : Type) [lie_ring M] [lie_algebra ℤ M] :=
-- sl2 with half-H 
(E : M) (H : M) (F : M)
-- circle 
(z : ℤ → (module.End ℤ M)) 
-- shift
(σ : lie_algebra.morphism ℤ M M)
-- involution 
(τ : lie_algebra.morphism ℤ M M)
-- structure
(str_sl2 : ⁅H, E⁆ = E ∧ ⁅F, E⁆ = 2 • H ∧ ⁅H, F⁆ = -F)
(str_circle : z 0 = linear_map.id ∧ ∀ (i j : ℤ), z i ∘ z j = z (i + j))
(str_invol : τ ∘ τ = id)
(invol_sl2 : τ E = -F ∧ τ H = -H ∧ τ F = -E)
(invol_circle : ∀ (i : ℤ), τ ∘ (z i) = z (-i) ∘ τ)
(invol_shift : τ ∘ σ = σ ∘ τ)
(sl2_shift : ∀ (m : M) (i : ℤ), 
               ⁅(z i) E, σ m⁆ = 0
             ∧ ⁅(z i) H, σ m⁆ = 0 
             ∧ ⁅(z i) F, σ m⁆ = 0)
(circle_shift : ∀ (m m' : M) (i j : ℤ), ⁅(z i) m, (z j) (σ m')⁆ = (z i) ⁅m, (z j) (σ m')⁆)
(sl2_circle : ∀ (i j : ℤ) (m : M), 
                ⁅(z i) E, (z j) m⁆ = j • (z (i+j+1)) m + (z j) ⁅(z i) E, m⁆ 
              ∧ ⁅(z i) H, (z j) m⁆ = j • (z (i+j  )) m + (z j) ⁅(z i) H, m⁆ 
              ∧ ⁅(z i) F, (z j) m⁆ = j • (z (i+j-1)) m + (z j) ⁅(z i) F, m⁆)

namespace ambient_module

variables {M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M]

instance ambient_invol : invol M := ⟨τ, str_invol⟩ 

def lift (f : gen → M) : words → M := 
words.rec f (λ a _ m, ⁅f a, m⁆)  

namespace lift

lemma ze : ∀ (f : gen → M) (a : gen), lift f (words.of a) = f a :=
begin
    intros, simp [lift, words.of, free_semigroup.of, words.rec, free_semigroup.rec_on] 
end

lemma su : ∀ (f : gen → M) (a : gen) (b : words), lift f (words.of a * b) = ⁅f a, lift f b⁆ :=
begin 
    intros, simp [lift, words.rec_su]
end

lemma invol 
    : ∀ (f : gen → M) (f_invol : ∀ (a : gen), f (gen.τ a) = τ (f a)) (w : words),
        lift f (invol.invol w) = τ (lift f w)
    :=
begin
    intros,
    let h :=  λ (b : words), lift f (invol.invol b) = invol.invol (lift f b),
    have hz : ∀ (a : gen), h (words.of a) :=
        begin
            intros,
            simp [h, lift],
            erewrite words.invol_of,
            simp [words.rec_ze],
            simp [f_invol],
            simp [invol.invol]
        end,
    have hs : ∀ (a : gen) (b : words), h (words.of a) → h b → h (words.of a * b) :=
        begin 
            intros, 
            simp [h] at a_2,
            simp [h],
            have ht : invol.invol (words.of a * b) = words.of a.τ * invol.invol b 
                    := by simpa [invol.invol, words.invol_of],
            simp [ht],
            repeat { erw lift.su },
            simp [a_2], 
            rw f_invol,
            simp [invol.invol]
        end,
    exact (free_semigroup.rec_on w hz hs)
end

end lift

def interpret_sl2_gen : gen → M
| gen.A  := E
| gen.A' := -F

def interpret_sl2 : words → M := lift interpret_sl2_gen

lemma interpret_sl2_gen_invol : ∀ (a : gen), interpret_sl2_gen (gen.τ a) = τ (interpret_sl2_gen a : M) :=
begin
    intros, cases a, 
    unfold gen.τ, unfold interpret_sl2_gen, simp [invol_sl2],
    unfold gen.τ, unfold interpret_sl2_gen, 
    have h : ∀ (x : M), τ (-x) = - τ x, swap, rw h, simp [invol_sl2],
    intros,
    exact (linear_map.map_neg (τ).to_linear_map x)
end 

lemma interpret_sl2_invol : ∀ (w : words), interpret_sl2 (invol.invol w) = invol.invol (interpret_sl2 w : M) :=
begin
    intros, unfold interpret_sl2, unfold invol.invol, 
    exact (lift.invol interpret_sl2_gen interpret_sl2_gen_invol w)
end

-- useful in rewriting expressions
lemma transposed_jacobi (x : M) : ∀ (y z : M), ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ :=
begin
    intros,
    rw ←(lie_skew x z), rw lie_neg,
    rw ←(lie_skew ⁅x, y⁆ z),
    rw add_comm,
    have h : ∀ (a b c : M), a + b + c = 0 → a = -b + -c := 
        begin
            intros, rw add_assoc at a_1, rw @eq_neg_of_add_eq_zero M _ a (b + c) a_1, simp [add_comm]  
        end,
    apply h, exact lie_ring.jacobi x y z,
end  

section zeta 

variable (ζ : M)

def interpret_gen : gen → M
| gen.A  := ζ
| gen.A' := τ ζ

def interpret  : words → M := lift (interpret_gen  ζ)

lemma interpret_ze : ∀  (a : gen), interpret ζ (words.of a) = interpret_gen ζ a :=
begin intros, unfold interpret, simp [lift.ze] end

lemma interpret_su : ∀  (a : gen) (b : words)
                   , interpret ζ (words.of a * b) = ⁅interpret_gen ζ a, interpret ζ b⁆ :=
begin intros, unfold interpret, simp [lift.su] end

lemma interpret_gen_invol : ∀  (a : gen), interpret_gen ζ (gen.τ a) = τ (interpret_gen ζ a) :=
begin
    intros, cases a, simpa [interpret_gen], rw (gen.τ), simp [interpret_gen],
    have h := str_invol,
    simp [function.comp] at h,
    apply_fun (λ (f : M → M), f ζ) at h,
    rw h
end 

lemma interpret_invol : ∀  (w : words), interpret ζ (invol.invol w) = invol.invol (interpret ζ w) :=
begin
    intros, unfold interpret, unfold invol.invol, 
    exact (lift.invol (interpret_gen ζ) (interpret_gen_invol ζ) w)
end

def serpentine : Prop := ζ = E + (z 1) (σ (ζ - H))

def serpentine_str_H  (hζ : serpentine ζ) : ⁅ H, ζ ⁆ = ζ :=
begin
    unfold serpentine at hζ,
    rw hζ,
    simp [lie_add, str_sl2],
    have h : (H : M) = (z 0) H := by simp [str_circle.1],
    rw h, 
    simp [sl2_circle],
    simp [(sl2_shift _ 0).2]
end

def serpentine_str_H' (hζ : serpentine ζ) : ⁅ H, τ ζ ⁆ = -(τ ζ) :=
begin
    intros,
    rw (_ : H = -(-H)),
    rw ←(invol_sl2.2.1),
    rw neg_lie,
    erw ←τ.map_lie,
    rw serpentine_str_H ζ hζ, 
    simp [coe_fn, has_coe_to_fun.coe],
    simp
end

/-
lemma interpret_wt (hζ : serpentine ζ) : ∀ (w : words), ⁅ H, interpret ζ w ⁆ = w.wt • interpret ζ w :=
begin
end
-/
end zeta




end ambient_module

-- ⁅    ⁆
