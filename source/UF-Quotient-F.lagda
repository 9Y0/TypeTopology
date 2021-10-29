Martin Escardo and Tom de Jong, October 2021

Modified from UF-Quotient.lagda to add the parameter F.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv

open import UF-PropTrunc-F
open import UF-ImageAndSurjection-F

module UF-Quotient-F
        (F   : Universe → Universe)
        (pt  : propositional-truncations-exist F)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

\end{code}

We define when a relation is subsingleton (or proposition) valued,
reflexive, transitive or an equivalence.

What is noteworthy, for the purpose of explaining universes in Agda to
Dan, is that X is in a universe 𝓤, and the value of the relation is in
a universe 𝓥, where 𝓤 and 𝓥 are arbitrary.

(NB. The Agda library uses the word "Level" for universes, and then
what we write "𝓤 ̇" here is written "Set 𝓤". This is not good for
univalent mathematics, because the types in 𝓤 ̇ need not be sets, and
also because it places emphasis on levels rather than universes
themselves.)

Then, for example, the function is-prop-valued defined below takes
values in the least upper bound of 𝓤 and 𝓥, which is denoted by 𝓤 ⊔ 𝓥.

We first define the type of five functions and then define them, where
_≈_ is a variable:

\begin{code}

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

\end{code}

Now, using an anonymous module with parameters (corresponding to a
section in Coq), we assume propositional truncations that stay in the
same universe, function extensionality for all universes, two
universes 𝓤 and 𝓥, propositional truncation for the universe 𝓥, a type
X : 𝓤 ̇, and an equivalence relation _≈_ with values in 𝓥 ̇.

\begin{code}

module quotient
       {𝓤 𝓥 : Universe}
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-prop-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open PropositionalTruncation F pt
 open ImageAndSurjection F pt

\end{code}

Now, Ω 𝓥 is the type of subsingletons, or (univalent) propositions, or
h-propositions, or mere propositions, in the universe 𝓥, which lives
in the next universe 𝓥 ⁺.

From the relation _≈_ : X → (X → 𝓥 ̇ ) we define a relation
X → (X → Ω 𝓥), which of course is formally a function. We then take
the quotient X/≈ to be the image of this function.

Of course, it is for constructing the image that we need propositional
truncations.

\begin{code}

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = x ≈ y , ≈p x y

\end{code}

Then the quotient lives in the least upper bound of 𝓤 and 𝓥 ⁺, where 𝓥 ⁺
is the successor of the universe 𝓥:

\begin{code}

 X/≈ : F (𝓤 ⊔ (𝓥 ⁺)) ⊔ 𝓤 ⊔ (𝓥 ⁺) ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
                (powersets-are-sets'' fe fe pe)
                ∥∥-is-prop

 η : X → X/≈
 η = corestriction equiv-rel

\end{code}

Then η is the universal solution to the problem of transforming
equivalence _≈_ into equality _≡_ (in Agda the notation for the
identity type is _≡_ - we can't use _=_ because this is a reserved
symbol for definitional equality).

By construction, η is a surjection, of course:

\begin{code}

 η-surjection : is-surjection η
 η-surjection = corestriction-is-surjection equiv-rel

\end{code}

It is convenient to use the following induction principle for
reasoning about the image. Notice that the property we consider has
values in any universe 𝓦 we please:

\begin{code}

 quotient-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
                    → ((x' : X/≈) → is-prop (P x'))
                    → ((x : X) → P (η x))
                    → (x' : X/≈) → P x'
 quotient-induction = surjection-induction η η-surjection

\end{code}

The first part of the universal property of η says that equivalent
points are mapped to equal points:

\begin{code}

 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e =
   to-Σ-≡ (dfunext fe
          (λ z → to-Σ-≡ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                         being-prop-is-prop fe _ _)) ,
       ∥∥-is-prop _ _)

\end{code}

We also need the fact that η reflects equality into equivalence:

\begin{code}

 η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ≡ (x ≈ y)
     a = ap (λ - → pr₁ (- y)) (q ⁻¹)
     b : (y ≈ y) → (x ≈ y)
     b = Idtofun a

\end{code}

We are now ready to formulate and prove the universal property of the
quotient. What is noteworthy here, regarding universes, is that the
universal property says that we can eliminate into any set A of any
universe 𝓦.

                   η
              X ------> X/≈
               \       .
                \     .
               f \   . f'
                  \ .
                   v
                   A

\begin{code}

 universal-property : ∀ {𝓦} (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ≡ f x')
                    → ∃! f' ꞉ ( X/≈ → A), f' ∘ η ≡ f
 universal-property {𝓦} A iss f pr = ic
  where
   φ : (x' : X/≈) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ x') × (f x ≡ a))
   φ = quotient-induction _ γ induction-step
     where
      induction-step : (y : X) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ η y) × (f x ≡ a))
      induction-step x (a , d) (b , e) = to-Σ-≡ (p , ∥∥-is-prop _ _)
       where
        h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a))
          → (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b))
          → a ≡ b
        h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ pr (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

        p : a ≡ b
        p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

      γ : (x' : X/≈) → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)))
      γ x' = being-prop-is-prop fe

   k : (x' : X/≈) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)
   k = quotient-induction _ φ induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ≡ f
   r = dfunext fe h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))) → f' (η y) ≡ f y
     j y (x , p , q) = q ⁻¹ ∙ pr (η-equal-equiv p)

     h : (y : X) → f' (η y) ≡ f y
     h y = ∥∥-rec iss (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-≡ (t , v)
    where
     w : ∀ x → f' (η x) ≡ f'' (η x)
     w = happly (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = dfunext fe (quotient-induction _ (λ _ → iss) w)

     u : f'' ∘ η ≡ f
     u = transport (λ - → - ∘ η ≡ f) t r

     v : u ≡ s
     v = Π-is-set fe (λ _ → iss) u s

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ≡ f
   ic = (f' , r) , c

\end{code}
