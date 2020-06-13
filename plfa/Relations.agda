import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- relations as indexed/dependent data types

-- This relation is decidable
-- see how to convert between using https://plfa.github.io/Decidable/
-- Recall in Coq Software Foundations, using a function resulting in
-- bool vs a relation in Prop

-- See 'reflect'
--Inductive reflect (P : Prop) : bool → Prop :=
--| ReflectT (H : P) : reflect P true
-- | ReflectF (H : ¬P) : reflect P false.

data  _≤_ : ℕ -> ℕ -> Set where
  z≤n : ∀ { n : ℕ }
      -----------
   ->  zero ≤ n

  s≤s : ∀ { m n : ℕ }
     ->  m ≤ n
     -----------
     ->  suc m ≤ suc n

_ : 2 ≤ 3
_ = s≤s (s≤s z≤n )

-- with explicit arguments
_ : 2 ≤ 3
_ = s≤s {1} {2} (s≤s {0} {1} (z≤n {1} ))

infix 4 _≤_
-- bind less tighly than +

-- inversion ('get the arguments passed in ')
-- Frequently used coq tactic
--In Coq, the constructors of inductive types are injective and disjoint.
-- injectivity allows for extraction of arguments
inv-s≤s : ∀ { m n : ℕ }
  -> suc m ≤ suc n
  ----------------
  -> m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  -> m ≤ zero
  -----------
  -> m ≡ zero
inv-z≤n z≤n = refl


-- Common Properties of ≤ relation
-- Reflexivity
-- Transitivity
-- Anti-Symmetry

≤-refl : ∀ {n : ℕ} -> n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc m} = s≤s ≤-refl


≤-trans : ∀ { n m p : ℕ }
  -> m ≤ n
  -> n ≤ p
  --------
  -> m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-anti-sym : ∀ { n m : ℕ }
  -> m ≤ n
  -> n ≤ m
  --------
  -> m ≡ n
≤-anti-sym z≤n z≤n = refl
≤-anti-sym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-anti-sym m≤n n≤m)


-- totality of ≤
-- could also be written with logical disjunction
data Total (m n : ℕ) : Set where
  forward : m ≤ n -> Total m n
  flipped : n ≤ m -> Total m n

≤-total : ∀ ( m n : ℕ ) -> Total m n
≤-total 0 _ = forward z≤n
≤-total _ 0 = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

-- equivalently, could define with a helper function
-- ≤-total (suc m) (suc n) = helper(≤-total m n)
--  helper : Total m n -> Total (suc m) (suc n
--  helper (forward m≤n) = forward (s≤s m≤n)
--  helper (flipped n≤m) = flipped (s≤s n≤m)

--≤-monotonic : ∀ {m n p q} -> m ≤ n -> p ≤ q -> m + p ≤ n + q
--≤-monotonic z≤n z≤n = z≤n
--≤-monotonic z≤n _ = {!   !}
--≤-monotonic _ _ = {!   !}

--
