module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)

open import plfa.Isomorphism using (_≃_; extensionality)



¬_ : Set -> Set -- intuitionistic inro
¬ A = A -> ⊥

¬-elim : ∀ {A : Set} -- contradition
  -> ¬ A
  -> A
  -------
  -> ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

-- A -> ¬ ¬ A in classical
-- A ≃ ¬ ¬ A in classical
¬¬-intro : ∀ {A : Set}
  -> A
  -------
  -> ¬ ¬ A
¬¬-intro x = λ{¬x -> ¬x x }

¬¬¬-elim : ∀ {A : Set}
  -> ¬ ¬ ¬ A
  ----------
  -> ¬ A
¬¬¬-elim ¬¬¬x = λ x -> ¬¬¬x (¬¬-intro x)


contraposition : ∀ {A B : Set}
  -> (A -> B)
  -----------
  -> (¬ B -> ¬ A)
contraposition f ¬y x = ¬y (f x)


_≢_ : ∀ {A : Set} -> A -> A -> Set
x ≢ y = ¬ (x ≡ y)

-- ¬ (1 ≡ 2)
-- (1 ≡ 2) -> ⊥
_ : 1 ≢ 2
_ = λ ()

-- () this is a constructor pattern that expresses
-- a term of this type doesn't exist

peano : ∀ {m : ℕ} -> zero ≢ suc m
peano = λ ()


-- 0 ^ 0 = 1
_ : ⊥ -> ⊥
_ = λ ()

-- any two proofs of a negation are equal
assimilation : ∀ {A : Set} (¬x ¬x' : ¬ A) -> ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality (λ x -> ⊥-elim(¬x x) )

Stable : Set -> Set
Stable A = ¬ ¬ A -> A






--
