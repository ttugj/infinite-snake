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

def interpret_gen (ζ : M) : gen → M
| gen.A  := ζ
| gen.A' := τ ζ

def interpret_sl2_gen : gen → M
| gen.A  := E
| gen.A' := -F

def interpret (ζ : M) : words → M := lift (interpret_gen  ζ)

def interpret_sl2 : words → M := lift interpret_sl2_gen

lemma interpret_ze : ∀ (ζ : M) (a : gen), interpret ζ (words.of a) = interpret_gen ζ a :=
begin intros, unfold interpret, simp [lift.ze] end

lemma interpret_su : ∀ (ζ : M) (a : gen) (b : words)
                   , interpret ζ (words.of a * b) = ⁅interpret_gen ζ a, interpret ζ b⁆ :=
begin intros, unfold interpret, simp [lift.su] end

lemma interpret_gen_invol : ∀ (ζ : M) (a : gen)
                          , interpret_gen ζ (gen.τ a) = τ (interpret_gen ζ a) :=
begin
    intros, cases a, simpa [interpret_gen], rw (gen.τ), simp [interpret_gen],
    have h := str_invol,
    simp [function.comp] at h,
    apply_fun (λ (f : M → M), f ζ) at h,
    rw h
end 

lemma interpret_sl2_gen_invol : ∀ (a : gen)
                              , interpret_sl2_gen (gen.τ a) = @id M (τ $ interpret_sl2_gen a) :=
begin
    intros, cases a, 
    unfold gen.τ, unfold interpret_sl2_gen, simp [invol_sl2],
    unfold gen.τ, unfold interpret_sl2_gen, 
    have h : ∀ (x : M), τ (-x) = - τ x, swap, rw h, simp [invol_sl2],
    intros,
    exact (linear_map.map_neg (τ).to_linear_map x)
end 

lemma interpret_invol : ∀ (ζ : M) (w : words), interpret ζ (invol.invol w) = invol.invol (interpret ζ w) :=
begin
    intros, unfold interpret, unfold invol.invol, 
    exact (lift.invol (interpret_gen ζ) (interpret_gen_invol ζ) w)
end

lemma interpret_sl2_invol : ∀ (w : words), interpret_sl2 (invol.invol w) = @id M (invol.invol $ interpret_sl2 w) :=
begin
    intros, unfold interpret_sl2, unfold invol.invol, 
    exact (lift.invol interpret_sl2_gen interpret_sl2_gen_invol w)
end

def serpentine (ζ : M) : Prop := (ζ = E + (z 1) (σ (ζ - H))) 

def serpentine_str_H (ζ : M) (hζ : serpentine ζ) : ⁅ H, ζ ⁆ = ζ :=
begin
  sorry
end

/-
lemma interpret_wt 
{M : Type} [lie_ring M] [lie_algebra ℤ M] [ambient_module M] 
(ζ : M) (hζ : serpentine ℤ ζ) : ∀ (w : words), ⁅ H k, interpret ℤ ζ w ⁆ = w.wt • interpret ℤ ζ w :=
begin
    intros, unfold interpret, unfold lift, induction w, induction w_snd, 
    -- base
    unfold words.rec, unfold words.wt, unfold free_semigroup.rec_on,   
    unfold words.rec, unfold free_semigroup.rec_on,
    cases w_fst,
    unfold interpret_gen, unfold words.wt_gen,
end
 -/

end ambient_module

-- ⁅    ⁆
