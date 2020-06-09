module plfa.Induction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)



-- cong : ∀ (f : A -> B ) {x y} -> x ≡ y -> f x ≡ f y

-- or in Arend
-- \func pmap {A B : \Type} {a a' : A} (f : A -> B) (p : a = a') : f a = f a' =>
--  path(\lam i => f (p @ i))

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
-- (0 + m) + n ≡ 0 + (m + n) => m + n ≡ m + n
+-assoc (suc m) n p = cong suc (+-assoc m n p)
  -- begin
    -- suc((m + n) + p)
  -- ≡⟨ cong suc (+-assoc m n p) ⟩ -- inductive step
    -- suc (m + (n + p))
  -- ∎

+-zlemma : ∀ (n : ℕ) -> n + 0 ≡ n
+-zlemma zero = refl
+-zlemma (suc m) = cong suc (+-zlemma m)

+-succ : ∀ (m n : ℕ) -> m + (suc n) ≡ suc (m + n)
+-succ zero n = refl
+-succ (suc m) n = cong suc (+-succ m n)

+-comm : ∀ (m n : ℕ) -> m + n ≡ n + m
+-comm m zero = +-zlemma m
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-succ m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
