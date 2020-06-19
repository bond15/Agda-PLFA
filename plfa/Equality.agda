module plfa.Equality where


data _≡_ {A : Set} (x : A): A -> Set where
  refl : x ≡ x

infix 4 _≡_

data Unit : Set where
  unit : Unit

_ : unit ≡ unit
_ = refl

data Bool : Set where
  tt : Bool
  ff : Bool

not : Bool -> Bool
not tt = ff
not ff = tt

_ : not tt ≡ ff
_ = refl

id₁ : Bool -> Bool
id₁ x = x

id₂ : Set -> Set
id₂ x = x

id₃ : Bool -> Bool
id₃ tt = tt
id₃ ff = ff

id₄ : Bool -> Bool
id₄ x = not (not x)

_ : id₁ ≡ id₁
_ = refl

-- id₁ not eq id₂ not eq id₃ not ed id₄


-- equality is an equivalence relations
-- Reflexivity: refl
-- Symmetry: sym
-- Transitivity

sym : ∀ {A : Set} {x y : A}
  -> x ≡ y
  -> y ≡ x
sym refl = refl


trans : ∀ {A : Set} {x y z : A}
  -> x ≡ y
  -> y ≡ z
  --------
  -> x ≡ z
trans refl refl = refl


-- congruence
cong : ∀ {A B : Set} (f : A -> B){x y : A}
  -> x ≡ y
  --------
  -> f x ≡ f y
cong f refl = refl

cong-app : ∀ {A B : Set} {f g : A -> B}
  -> f ≡ g
  --------
  -> ∀ (x : A) -> f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A -> Set)
  -> x ≡ y
  --------
  -> P x -> P y
subst P refl px = px


module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A}
    -> x ≡ y
    --------
    -> x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) { y : A}
    -> x ≡ y
    --------
    -> x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A){y z : A}
    -> x ≡ y
    -> y ≡ z
    --------
    -> x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
    -------
    -> x ≡ x
  x ∎ = refl
open ≡-Reasoning



--Note the above is equality in MLTT

-- Leibniz equality
-- two objects are equal iff they satisfy the same properties
_≐_ : ∀ {A : Set} (x y : A) -> Set₁
_≐_ {A} x y = ∀ (P : A -> Set) -> P x -> P y

-- see Leibniz equality is isomorphic to Martin-Lof Identity, Parametrically
-- this can be shown in agda



-- Universe Polymorphism
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)


data Maybe (A : Set₀) : Set₁ where
  just : A -> Maybe A
  nothing : Maybe A


-- can't compare these because the live in Set₂ and our MLTT Identity (≡) was
-- defined for Set or Set₀
--_ : nothing ≡ nothing
--_ = refl

-- generalize to any universe level
data _≡'_ { ℓ : Level} {A : Set ℓ} (x : A) : A -> Set ℓ where
  refl' : x ≡' x

-- now this works
_ : nothing ≡' nothing
_ = refl'


-- composition at Set₀

_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

_ : (not ∘ not) tt ≡ tt
_ = refl


-- but you cant do
fmap : ∀ {A B : Set₀} -> (A -> B) -> Maybe A -> Maybe B
fmap f nothing = nothing
fmap f (just a) = just (f a)

-- requires a definition of compositioon that is universe polymorphic
-- (or at least up to Set₁)
--_ : fmap (id₂ ∘ id₂) nothing ≡ nothing
--_ = refl

_∘'_ : ∀ { ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} ->
  (B -> C) -> (A -> B) -> A -> C
(g ∘' f) a = g (f a)


id :  ∀ {ℓ : Level} {A : Set ℓ } -> A -> A
id a = a

-- now you can do
x = fmap (id ∘' id) nothing
