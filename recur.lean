import algebra.lie_algebra
import algebra.module
import data.finsupp
import linear_algebra.finsupp

import .words
import .ambient

noncomputable theory

namespace words

def mod (R : Type) [ring R] := words →₀ R 

namespace mod

variables {R : Type} [ring R]

instance : add_comm_group (mod R) := @finsupp.add_comm_group words R _
instance : module R (mod R) := @finsupp.module words R _ _ _ _

def univ {A : Type} [add_comm_group A] [module R A] (φ : words → A) : mod R →ₗ[R] A 
:= finsupp.total words A R φ

end mod

end words

def phrases := words.mod int

#check phrases
