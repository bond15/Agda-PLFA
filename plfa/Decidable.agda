module plfa.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import plfa.Relations using (_≤_; z≤n; s≤s)
open import plfa.Isomorphism using(_⇔_)


-- a decidable version of _≤_

data Bool : Set where
  true : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ -> ℕ -> Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- computes via decision procedure
_ : (2 ≤ᵇ 4) ≡ true
_ = refl

-- hand made proof term
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- Relating evidence and computation
-- reflect boolean values into top and bottom
T : Bool -> Set
T true = ⊤
T false = ⊥

-- T b is inhabited when b ≡ true
T→≡ : ∀ (b : Bool) -> T b -> b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} -> b ≡ true -> T b
≡→T refl = tt


-- main idea!
-- show T (m ≤ᵇ n) is inhabited iff m ≤ n

-- recursively construct m ≤ n term
≤ᵇ→≤ : ∀ (m n : ℕ) -> T (m ≤ᵇ n) -> m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) zero ()
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

_ : 2 ≤ 4
_ = ≤ᵇ→≤ 2 4 tt -- s≤s (s≤s z≤n)


-- recursively deconstruct term
≤→≤ᵇ : ∀ {m n : ℕ} -> m ≤ n -> T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt --zero ≤ᵇ n
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n


_ : T (2 ≤ᵇ 4)
_ = ≤→≤ᵇ {2} {4} (s≤s (s≤s z≤n))



data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : ¬ A -> Dec A


¬s≤z : ∀ {m : ℕ} -> ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} -> ¬ (m ≤ n) -> ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n


-- recuse all the way to the bottom, peeling constructors along the way
-- arrive at either the yes or no base cases
-- build up a proof of yes or no
_≤?_ : ∀ (m n : ℕ) -> Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
...                | yes m≤n = yes (s≤s m≤n)
...                | no ¬m≤n = no (¬s≤s ¬m≤n)


p : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
p = refl

¬p : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
¬p = refl






--
