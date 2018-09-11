Martin Escardo 2012.

We investigate coinduction and corecursion on ℕ∞, the generic
convergent sequence.

We show that set ℕ∞ satisfies the following universal property for a
suitable P : ℕ∞ → 𝟙 + ℕ∞, where 𝟙 is the singleton type
with an element *.

For every type X and every p : X → 𝟙 + X there is a unique h : X → ℕ∞
such that

                        p
             X ------------------> 𝟙 + X
             |                       |
             |                       |
          h  |                       | 𝟙 + h
             |                       |
             |                       |
             v                       v
             ℕ∞ -----------------> 𝟙 + ℕ∞
                        P

The maps p and P are called coalgebras for the functor 𝟙 + (-), and
the above diagram says that h is a coalgebra morphism from p to P.

In equational form, this is

             P ∘ h ≡ (𝟙 + h) ∘ p,

which can be considered as a corecursive definition of h.  The map P
(a sort of predecessor function) is an isomorphism with inverse S (a
sort of successor function). This follows from Lambek's Lemma once the
above universal property is established, but we actually need to know
this first in order to prove the universal property.

             S : 𝟙 + ℕ∞ → ℕ∞
             S(in₀ *) = Zero
             S(in₁ u) = Succ u

Using this fact, the above corecursive definition of h is equivalent
to:

             h ≡ S ∘ (𝟙 + h) ∘ p

or

             h(x) ≡ S((𝟙 + h)(p x)).

Now p x is either of the form in₀ * or in₁ x' for a unique x' : X, and
hence the above equation amounts to

             h(x) ≡ Zero,           if p x ≡ in₀ *,
             h(x) ≡ Succ(h x'),     if p x ≡ in₁ x',

once we know the definition of 𝟙 + h. This shows more clearly how the
diagram can be considered as a (co)recursive definition of h, and
indicates how h may be constructed.

In order to show that any two functions that make the above diagram
commute are unique, that is, that the above two conditional equations
uniquely determine h, we develop a coinduction principle based on
bisimulations. This gives a technique for establishing equalities on
ℕ∞.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module CoNaturals (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import Two
open import GenericConvergentSequence

Zero' : 𝟙 + ℕ∞
Zero' = inl {U₀} {U₀} *

Pred' : ℕ∞ → 𝟙 + ℕ∞
Pred' u = inr {U₀} {U₀} (Pred u)

P : ℕ∞ → 𝟙 + ℕ∞
P u = 𝟚-cases Zero' (Pred' u) (positivity u)

P-Zero : P Zero ≡ Zero'
P-Zero = refl

P-Succ : (u : ℕ∞) → P(Succ u) ≡ inr u
P-Succ u = ap inr Pred-Succ

S : 𝟙 {U₀} + ℕ∞ → ℕ∞
S(inl *) = Zero
S(inr u) = Succ u

P-S-id : {y : 𝟙 + ℕ∞} → P(S y) ≡ y
P-S-id{inl *} = refl
P-S-id{inr u} = refl

S-lc : {y z : 𝟙 + ℕ∞} → S y ≡ S z → y ≡ z
S-lc r = P-S-id ⁻¹ ∙ ap P r ∙ P-S-id

S-P-id : {u : ℕ∞} → S(P u) ≡ u
S-P-id {u} = 𝟚-equality-cases l₀ l₁
 where
  l₀ : positivity u ≡ ₀ → S(P u) ≡ u
  l₀ r = c₁ ∙ (is-Zero-equal-Zero (fe U₀ U₀) r)⁻¹
    where
     c₀ : P u ≡ Zero'
     c₀ = ap (𝟚-cases Zero' (Pred' u)) r
     c₁ : S(P u) ≡ Zero
     c₁ = ap S c₀
  l₁ : positivity u ≡ ₁ → S(P u) ≡ u
  l₁ r = c₁ ∙ c₃ ⁻¹
   where
     c₀ : P u ≡ Pred' u
     c₀ = ap (𝟚-cases Zero' (Pred' u)) r
     c₁ : S(P u) ≡ Succ(Pred u)
     c₁ = ap S c₀
     c₂ : u ≢ Zero
     c₂ s = Lemma[b≡₀→b≢₁](ap positivity s) r
     c₃ : u ≡ Succ(Pred u)
     c₃ = not-Zero-is-Succ (fe U₀ U₀) c₂

P-lc : {u v : ℕ∞} → P u ≡ P v → u ≡ v
P-lc r = S-P-id ⁻¹ ∙ ap S r ∙ S-P-id

𝟙+ : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → 𝟙 + X → 𝟙 + Y
𝟙+ f (inl s) = inl {U₀} s
𝟙+ f (inr x) = inr(f x)

diagram-commutes : ∀ {U} {X : U ̇} → (X → 𝟙 + X) → (X → ℕ∞) → U ̇
diagram-commutes p h = (P ∘ h ≡ (𝟙+ h) ∘ p)

coalg-mophism→ : ∀ {U} {X : U ̇} (p : X → 𝟙 + X) (h : X → ℕ∞)
               → diagram-commutes p h
               → h ≡ S ∘ (𝟙+ h) ∘ p
coalg-mophism→ {U} p h a = dfunext (fe U U₀)
                          (λ x → S-P-id ⁻¹ ∙ ap (λ - → S(- x)) a)

coalg-mophism← : ∀ {U} {X : U ̇} (p : X → 𝟙 + X) (h : X → ℕ∞)
               → h ≡ S ∘ (𝟙+ h) ∘ p
               → diagram-commutes p h
coalg-mophism← {U} p h b = dfunext (fe U U₀)
                            (λ x → ap (λ - → P(- x)) b ∙ P-S-id)

homomorphism-existence : ∀ {U} {X : U ̇} (p : X → 𝟙 + X)
                       → Σ \(h : X → ℕ∞) → diagram-commutes p h
homomorphism-existence {U} {X} p = h , dfunext (fe U U₀) h-spec
 where
  q : 𝟙 + X → 𝟙 + X
  q(inl s) = inl s
  q(inr x) = p x

  Q : ℕ → 𝟙 + X → 𝟙 + X
  Q 0 z = z
  Q(succ n) z = q(Q n z)

  E : 𝟙 + X → 𝟚
  E(inl s) = ₀
  E(inr x) = ₁

  hl : (z : 𝟙 + X) → E(q z) ≡ ₁ → E z ≡ ₁
  hl (inl s) r = r
  hl (inr x) r = refl

  h : X → ℕ∞
  h x = ((λ i → E(Q(succ i) (inr x))) ,
          λ i → hl(Q(succ i) (inr x)))

  h-spec : (x : X) → P(h x) ≡ (𝟙+ h)(p x)
  h-spec x = equality-cases (p x) l₀ l₁
   where
    l₀ : (s : 𝟙) → p x ≡ inl s → P(h x) ≡ (𝟙+ h)(p x)
    l₀ * r = c₂ ∙ c₀ ⁻¹
     where
      c₀ : (𝟙+ h)(p x) ≡ Zero'
      c₀ = ap (𝟙+ h) r
      c₁ : h x ≡ Zero
      c₁ = is-Zero-equal-Zero (fe U₀ U₀) (ap E r)
      c₂ : P(h x) ≡ Zero'
      c₂ = ap P c₁ ∙ P-Zero

    l₁ : (x' : X) → p x ≡ inr x' → P(h x) ≡ (𝟙+ h)(p x)
    l₁ x' r = c₆ ∙ c₀ ⁻¹
     where
      c₀ : (𝟙+ h)(p x) ≡ inr(h x')
      c₀ = ap (𝟙+ h) r
      c₁ : (n : ℕ) → q(Q n (inr x)) ≡ Q n (p x)
      c₁ 0 = refl
      c₁ (succ n) = ap q (c₁ n)
      c₂ : (n : ℕ) → q(Q n (inr x)) ≡ Q n (inr x')
      c₂ n = c₁ n ∙ ap (Q n) r
      c₃ : (n : ℕ) → E(q(Q n (inr x))) ≡ E(Q n (inr x'))
      c₃ n = ap E (c₂ n)
      c₄ : (i : ℕ) → incl(h x) i ≡ incl(Succ(h x')) i
      c₄ 0  = c₃ 0
      c₄ (succ i) = c₃(succ i)
      c₅ : h x ≡ Succ(h x')
      c₅ = incl-lc (fe U₀ U₀) (dfunext (fe U₀ U₀) c₄)

      c₆ : P(h x) ≡ inr(h x')
      c₆ = ap P c₅

ℕ∞-corec  : ∀ {U} {X : U ̇} → (X → 𝟙 + X) → (X → ℕ∞)
ℕ∞-corec p = pr₁(homomorphism-existence p)

ℕ∞-corec-diagram : ∀ {U} {X : U ̇} (p : X → 𝟙 + X)
                 → diagram-commutes p (ℕ∞-corec p)
ℕ∞-corec-diagram p = pr₂(homomorphism-existence p)

\end{code}

We now discuss coinduction. We first define bisimulations.

\begin{code}

ℕ∞-bisimulation : ∀ {U} → (ℕ∞ → ℕ∞ → U ̇) → U ̇
ℕ∞-bisimulation R = (u v : ℕ∞) → R u v
                                → (positivity u ≡ positivity v)
                                ×  R (Pred u) (Pred v)

ℕ∞-coinduction : ∀ {U} (R : ℕ∞ → ℕ∞ → U ̇) → ℕ∞-bisimulation R
               → (u v : ℕ∞) → R u v → u ≡ v
ℕ∞-coinduction R b u v r = incl-lc (fe U₀ U₀) (dfunext (fe U₀ U₀) (l u v r))
 where
  l : (u v : ℕ∞) → R u v → (i : ℕ) → incl u i ≡ incl v i
  l u v r 0 =  pr₁(b u v r)
  l u v r (succ i) = l (Pred u) (Pred v) (pr₂(b u v r)) i

\end{code}

To be able to use it for our purpose, we need to investigate
coalgebra homomorphisms in more detail.

\begin{code}

coalg-morphism-Zero : ∀ {U} {X : U ̇}
                      (p : X →  𝟙 + X) (h : X → ℕ∞)
                    → diagram-commutes p h
                    → (x : X) (s : 𝟙) → p x ≡ inl s → h x ≡ Zero
coalg-morphism-Zero p h a x * c = S-P-id ⁻¹ ∙ ap S c₃
 where
  c₁ : P(h x) ≡ (𝟙+ h)(p x)
  c₁ = ap (λ - → - x) a
  c₂ : (𝟙+ h)(p x) ≡ Zero'
  c₂ = ap (𝟙+ h) c
  c₃ : P(h x) ≡ inl *
  c₃ = c₁ ∙ c₂

coalg-morphism-Succ : ∀ {U} {X : U ̇}
                      (p : X →  𝟙 + X) (h : X → ℕ∞)
                    → diagram-commutes p h
                    → (x x' : X) → p x ≡ inr x' → h x ≡ Succ(h x')
coalg-morphism-Succ p h a x x' c = S-P-id ⁻¹ ∙ ap S c₃
 where
  c₁ : P(h x) ≡ (𝟙+ h)(p x)
  c₁ = ap (λ - → - x) a
  c₂ : (𝟙+ h)(p x) ≡ inr(h x')
  c₂ = ap (𝟙+ h) c
  c₃ : P(h x) ≡ inr(h x')
  c₃ = c₁ ∙ c₂

\end{code}

The following two technical lemmas are used to construct a
bisimulation:

\begin{code}

coalg-morphism-positivity : ∀ {U} {X : U ̇}
                            (p : X →  𝟙 + X) (f g : X → ℕ∞)
                          → diagram-commutes p f
                          → diagram-commutes p g
                          → (x : X) → positivity(f x) ≡ positivity(g x)
coalg-morphism-positivity {U} {X} p f g a b x =
 equality-cases (p x) l₀ l₁
 where
  l₀ : (s : 𝟙) → p x ≡ inl s → positivity(f x) ≡ positivity(g x)
  l₀ s c = fl ∙ gl ⁻¹
   where
    fl : positivity(f x) ≡ ₀
    fl = ap positivity(coalg-morphism-Zero p f a x s c)
    gl : positivity(g x) ≡ ₀
    gl = ap positivity(coalg-morphism-Zero p g b x s c)

  l₁ : (x' : X) → p x ≡ inr x' → positivity(f x) ≡ positivity(g x)
  l₁ x' c = fl ∙ gl ⁻¹
   where
    fl : positivity(f x) ≡ ₁
    fl = ap positivity(coalg-morphism-Succ p f a x x' c)
    gl : positivity(g x) ≡ ₁
    gl = ap positivity(coalg-morphism-Succ p g b x x' c)

coalg-morphism-Pred : ∀ {U} {X : U ̇}
                      (p : X →  𝟙 + X) (f g : X → ℕ∞)
                    → diagram-commutes p f
                    → diagram-commutes p g
                    → (x : X) (u v : ℕ∞)
                    → u ≡ f x
                    → v ≡ g x
                    → Σ \(x' : X) → (Pred u ≡ f x') × (Pred v ≡ g x')
coalg-morphism-Pred {U} {X} p f g a b x u v d e =
 equality-cases (p x) l₀ l₁
 where
  l₀ : (s : 𝟙) → p x ≡ inl s
     → Σ \x' → (Pred u ≡ f x') ×  (Pred v ≡ g x')
  l₀ s c = x , (l f a u d , l g b v e)
   where
    l : (h : X → ℕ∞) → P ∘ h ≡ (𝟙+ h) ∘ p
      → (u : ℕ∞) → u ≡ h x → Pred u ≡ h x
    l h a u d = c₁ ∙ c₀ ⁻¹
     where
      c₀ : h x ≡ Zero
      c₀ = coalg-morphism-Zero p h a x s c
      c₁ : Pred u ≡ Zero
      c₁ = ap Pred (d ∙ c₀)

  l₁ : (x' : X) → p x ≡ inr x'
     → Σ \x' → (Pred u ≡ f x') × (Pred v ≡ g x')
  l₁ x' c = x' , ((l f a u d ) , (l g b v e ))
   where
    l : (h : X → ℕ∞) → P ∘ h ≡ (𝟙+ h) ∘ p
      → (u : ℕ∞) → u ≡ h x → Pred u ≡ h x'
    l h a u d = ap Pred d ∙ l'
     where
      l' : Pred(h x) ≡ h x'
      l' = ap Pred(coalg-morphism-Succ p h a x x' c)

\end{code}

We are finally able to prove the uniqueness of coalgebra homomorphisms
from p to P.

\begin{code}

homomorphism-uniqueness : ∀ {U} {X : U ̇}
                          (p : X → 𝟙 + X) (f g : X → ℕ∞)
                        → diagram-commutes p f
                        → diagram-commutes p g
                        → f ≡ g
homomorphism-uniqueness {U} {X} p f g a b = dfunext (fe U U₀) l
 where
  R : ℕ∞ → ℕ∞ → U ̇
  R u v = Σ \x → (u ≡ f x)  ×  (v ≡ g x)

  r : (x : X) → R (f x) (g x)
  r x = (x , refl , refl)

  R-positivity : (u v : ℕ∞) → R u v → positivity u ≡ positivity v
  R-positivity u v (x , c , d) = ap positivity c ∙ e ∙ ap positivity (d ⁻¹)
   where
    e : positivity(f x) ≡ positivity(g x)
    e = coalg-morphism-positivity {U} {X} p f g a b x

  R-Pred : (u v : ℕ∞) → R u v → R (Pred u) (Pred v)
  R-Pred u v (x , c , d) =
   (pr₁ l , pr₁(pr₂ l) , pr₂(pr₂ l))
   where
    l : Σ \x' → (Pred u ≡ f x') × (Pred v ≡ g x')
    l = coalg-morphism-Pred p f g a b x u v c d

  R-bisimulation : ℕ∞-bisimulation R
  R-bisimulation u v r = (R-positivity u v r) , (R-Pred u v r)

  l : f ∼ g
  l x = ℕ∞-coinduction R R-bisimulation (f x) (g x) (r x)

\end{code}

Putting existence and uniqueness together, we get that P is the final
coalgebra, as claimed:

\begin{code}

P-is-the-final-coalgebra : ∀ {U} {X : U ̇}
  → (p : X → 𝟙 + X) → Σ! \(h : X → ℕ∞) → diagram-commutes p h
P-is-the-final-coalgebra p = homomorphism-existence p , homomorphism-uniqueness p

\end{code}

There is more formalization work to do (2017): By now we know that Σ!
(a form of unique existence) is better captured by the contractibility
of Σ type (added 13th July 2018):

\begin{code}

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

P-is-the-homotopy-final-coalgebra : ∀ {U} {X : U ̇} (p : X → 𝟙 + X)
  → is-singleton(Σ \(h : X → ℕ∞) → diagram-commutes p h)
P-is-the-homotopy-final-coalgebra {U} {X} p = homomorphism-existence p , γ
 where
  γ : (e : Σ \(h' : X → ℕ∞) → diagram-commutes p h') → homomorphism-existence p ≡ e
  γ (h' , r) = to-Σ-≡
                (homomorphism-uniqueness p (ℕ∞-corec p) h' (ℕ∞-corec-diagram p) r ,
                 Π-is-set (fe U U₀)
                   (λ _ → +-is-set 𝟙 ℕ∞
                           (prop-is-set 𝟙-is-prop)
                           (ℕ∞-is-set (fe U₀ U₀))) _ _)

\end{code}
