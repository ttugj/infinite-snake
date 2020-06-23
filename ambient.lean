import algebra.lie_algebra
import algebra.module
import algebra.free
import control.functor
import tactic

import .words

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

variables (k : Type) [comm_ring k]

instance ambient_invol {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] : invol M :=
⟨@τ k _ _ _ _ _, @str_invol k _ _ _ _ _⟩ 

def is_serpentine 
{M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M]  -- lots of instances here...
(ζ : M) : Prop :=
(ζ = E k + (@z k _ _ _ _ _ 1) (@σ k _ _ _ _ _ (ζ - H k))) 

def interpret_gen {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] (ζ : M) : gen → M
| gen.A  := ζ
| gen.A' := @τ k _ _ _ _ _ ζ

def interpret {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] (ζ : M) : words → M := 
words.rec (interpret_gen k ζ) (λ a _ m, ⁅interpret_gen k ζ a, m⁆)  

lemma interpret_of {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (a : gen), interpret k ζ (words.of a) = interpret_gen k ζ a :=
begin
    intros, simp [interpret, words.of, free_semigroup.of, words.rec, free_semigroup.rec_on] 
end

lemma interpret_su {M :Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (a : gen) (b : words), interpret k ζ (words.of a * b) = ⁅interpret_gen k ζ a, interpret k ζ b⁆ :=
begin 
    intros, simp [interpret, words.rec_su]
end

lemma interpret_gen_invol {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] : 
    ∀ (ζ : M) (a : gen), interpret_gen k ζ (gen.τ a) = @τ k _ _ _ _ _ (interpret_gen k ζ a) :=
begin
    intros, cases a, simpa [interpret_gen], rw (gen.τ), simp [interpret_gen],
    have h := @str_invol k M _ _ _ _,
    simp [function.comp] at h,
    apply_fun (λ (f : M → M), f ζ) at h,
    rw h
end 

lemma interpret_invol  {M : Type} [lie_ring M] [lie_algebra k M] [ambient_module k M] :
    ∀ (ζ : M) (w : words), interpret k ζ (invol.invol w) = invol.invol (interpret k ζ w)
:= 
begin
    intros,
    let h :=  λ (b : words), interpret k ζ (invol.invol b) = invol.invol (interpret k ζ b),
    have hz : ∀ (a : gen), h (words.of a) :=
        begin
            intros,
            simp [h, interpret],
            erewrite words.invol_of,
            simp [words.rec_ze],
            simp [interpret_gen_invol],
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
            repeat { erw interpret_su },
            simp [a_2], 
            rw interpret_gen_invol,
            simp [invol.invol]
        end,
    exact (@free_semigroup.rec_on 
                gen 
                (λ (w' : words), interpret k ζ (invol.invol w') = invol.invol (interpret k ζ w')) 
                w hz hs),
end

end ambient_module
