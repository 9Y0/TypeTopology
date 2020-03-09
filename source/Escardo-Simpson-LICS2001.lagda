Todd Waugh Ambridge and Martin Escardo, 2nd March 2020.

We formalize, in univalent mathematics in Agda, some definitions in

M.H. Escardo and A. Simpson. A universal characterization of the
closed Euclidean interval (extended abstract). Proceedings of the 16th
Annual IEEE Symposium on Logic in Computer Science,
pp.115--125. Boston, Massachusetts, June 16-19, 2001.

https://www.cs.bham.ac.uk/~mhe/papers/lics2001-revised.pdf
https://www.cs.bham.ac.uk/~mhe/papers/interval.pdf
https://www.cs.bham.ac.uk/~mhe/.talks/map2011/

TODO. (Important.) The "double" stuff is not included yet.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Escardo-Simpson-LICS2001 where

open import SpartanMLTT
open import UF-Subsingletons

mid-point-algebra-axioms : (A : 𝓤 ̇ ) → (A → A → A) → 𝓤 ̇
mid-point-algebra-axioms {𝓤} A _⊕_ = is-set A × idempotency × commutativity × transposition
 where
  idempotency   = (x : A) → x ⊕ x ≡ x
  commutativity = (x y : A) → x ⊕ y ≡ y ⊕ x
  transposition = (x y u v : A) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)

cancellative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
cancellative _⊕_ = ∀ x y z → x ⊕ z ≡ y ⊕ z → x ≡ y

iterative : {A : 𝓤 ̇ } → (A → A → A) → 𝓤 ̇
iterative {𝓤} {A} _⊕_ = Σ M ꞉ ((ℕ → A) → A) , ((a : ℕ → A) → M a ≡ a 0 ⊕ M (a ∘ succ))
                                            × ((a x : ℕ → A) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i))
                                                             → a 0 ≡ M x)

\end{code}

We probably won't need the definition of Mid-point-algebra, but here
it is, for the record:

\begin{code}

Mid-point-algebra : (𝓤 : Universe) → 𝓤 ⁺ ̇
Mid-point-algebra 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)

Convex-body : (𝓤 : Universe) → 𝓤 ⁺ ̇
Convex-body 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ _⊕_ ꞉ (A → A → A) , (mid-point-algebra-axioms A _⊕_)
                                                 × (cancellative _⊕_)
                                                 × (iterative _⊕_)

⟨_⟩ : Convex-body 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A

mid-point-operation : (𝓐 : Convex-body 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
mid-point-operation (A , _⊕_ , _) = _⊕_

syntax mid-point-operation 𝓐 x y = x ⊕⟨ 𝓐 ⟩ y


is-homomorphism : (𝓐 : Convex-body 𝓤) (𝓑 : Convex-body 𝓥)
                → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-homomorphism 𝓐 𝓑 h = ((x y : ⟨ 𝓐 ⟩) → h (x ⊕⟨ 𝓐 ⟩ y) ≡ h x ⊕⟨ 𝓑 ⟩ h y)

id-is-homomorphism : (𝓐 : Convex-body 𝓤)
                   → is-homomorphism 𝓐 𝓐 id
id-is-homomorphism 𝓐 = {!!}



is-interval-object : (𝓘 : Convex-body 𝓤) → ⟨ 𝓘 ⟩ → ⟨ 𝓘 ⟩ → 𝓤ω
is-interval-object {𝓤} 𝓘 u v =

     {𝓥 : Universe} (𝓐 : Convex-body 𝓥) (a b : ⟨ 𝓐 ⟩)
   → ∃! h ꞉ (⟨ 𝓘 ⟩ → ⟨ 𝓐 ⟩) , (h u ≡ a)
                            × (h v ≡ b)
                            × ((x y : ⟨ 𝓘 ⟩) → h (x ⊕⟨ 𝓘 ⟩ y) ≡ h x ⊕⟨ 𝓐 ⟩ h y)


record interval-object-exists (𝓤 : Universe) : 𝓤ω where
 field
  𝕀 : 𝓤 ̇
  _⊕_ : 𝕀 → 𝕀 → 𝕀
  u v : 𝕀
  mpaa : mid-point-algebra-axioms 𝕀 _⊕_
  ca : cancellative _⊕_
  ia : iterative _⊕_
  universal-property : is-interval-object (𝕀 , _⊕_ , mpaa , ca , ia) u v

\end{code}

TODO. being-interval-object-is-prop.

TODO. We need to axiomatize the existence of double (page 33 and
onwards of the slides).

\begin{code}

module basic-interval-object-development {𝓤 : Universe} (io : interval-object-exists 𝓤) where

 open interval-object-exists io public

 ⊕-idem : (x : 𝕀) → x ⊕ x ≡ x
 ⊕-idem = pr₁ (pr₂ mpaa)

 ⊕-comm : (x y : 𝕀) → x ⊕ y ≡ y ⊕ x
 ⊕-comm = pr₁ (pr₂ (pr₂ mpaa))

 ⊕-tran : (x y u v : 𝕀) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)
 ⊕-tran = pr₂ (pr₂ (pr₂ mpaa))

 ⊕-canc : (x y z : 𝕀) → x ⊕ z ≡ y ⊕ z → x ≡ y
 ⊕-canc = interval-object-exists.ca io

 𝓘 : Convex-body 𝓤
 𝓘 = 𝕀 , _⊕_ , mpaa , ⊕-canc , ia


\end{code}

To be continued.

In this submodule, we should develop the basic theory of the interval
object, with the constructions and theorems of the slides.

  * affine (page 11)

\begin{code}

 affine : 𝕀 → 𝕀 → 𝕀 → 𝕀
 affine x y = ∃!-witness (universal-property 𝓘 x y)

 affine-equation-l : ∀ (x y : 𝕀) → affine x y u ≡ x
 affine-equation-l x y = pr₁ (∃!-is-witness (universal-property 𝓘 x y))

 affine-equation-r : ∀ (x y : 𝕀) → affine x y v ≡ y
 affine-equation-r x y = pr₁ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-is-midpoint-hom : ∀ (x y : 𝕀) → (a b : 𝕀) → affine x y (a ⊕ b) ≡ affine x y a ⊕ affine x y b
 affine-is-midpoint-hom x y = pr₂ (pr₂ (∃!-is-witness (universal-property 𝓘 x y)))

 affine-uniqueness : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-homomorphism 𝓘 𝓘 f
                   → affine a b ≡ f
 affine-uniqueness f a b l r i = ap pr₁ (∃!-uniqueness' (universal-property 𝓘 a b) (f , l , r , i))

 affine-uniqueness· : (f : 𝕀 → 𝕀) (a b : 𝕀)
                   → f u ≡ a
                   → f v ≡ b
                   → is-homomorphism 𝓘 𝓘 f
                   → affine a b ∼ f
 affine-uniqueness· f a b l r i x = ap (λ - → - x) ( affine-uniqueness f a b l r i)

 h-prop₄ : affine u v ≡ id
 h-prop₄ = affine-uniqueness id u v refl refl (id-is-homomorphism 𝓘)

 h-prop₅ : (a : 𝕀) → affine a a ≡ λ _ → a
 h-prop₅ a = affine-uniqueness (λ _ → a) a a refl refl (λ x y → {!!})

\end{code}

  * M (given in the iteration axiom)
    (By the way, we should prove that M is unique.)

  * Equational logic of M in page 16.

\begin{code}

 M : (ℕ → 𝕀) → 𝕀
 M = pr₁ ia

 M-prop₁ : (a : ℕ → 𝕀) → M a ≡ a 0 ⊕ (M (a ∘ succ))
 M-prop₁ = pr₁ (pr₂ ia)

 M-prop₂ : (a x : ℕ → 𝕀) → ((i : ℕ) → a i ≡ x i ⊕ a (succ i)) → a 0 ≡ M x
 M-prop₂ = pr₂ (pr₂ ia)

 M-idem : ∀ (x : 𝕀) → M (λ _ → x) ≡ x
 M-idem x = M-prop₂ (λ _ → x) (λ _ → x) (λ _ → ⊕-idem x ⁻¹) ⁻¹

 M-symm : ∀ (x : ℕ → ℕ → 𝕀) → M (λ i → (M λ j → x i j)) ≡ M (λ i → M (λ j → x j i))
 M-symm x = {!!}

 M-homo : ∀ x y → (M x ⊕ M y) ≡ M (λ i → x i ⊕ y i)
 M-homo x y = {!!}

-- (x y u v : 𝕀) → (x ⊕ y) ⊕ (u ⊕ v) ≡ (x ⊕ u) ⊕ (y ⊕ v)

\end{code}

  * A homomorphism of _⊕_ is automatically an M homomorphism (page 17)

\begin{code}

 open import NaturalsAddition renaming (_+_ to _+ℕ_)

 hom→hom : (h : 𝕀 → 𝕀)
           → ((x y : 𝕀) → h(x ⊕ y) ≡ h x ⊕ h y)
           → (z : ℕ → 𝕀) → h (M z) ≡ M (λ n → h (z n))
 hom→hom h hom z = M-prop₂ M' (λ n → h (z n)) γ where
   M' : ℕ → 𝕀
   M' 0 = h (M λ n → z n)
   M' (succ i) = h (M λ n → z (succ (n +ℕ i)))
   γ : (i : ℕ) → M' i ≡ (h (z i) ⊕ M' (succ i))
   γ zero = ap h (M-prop₁ z)
          ∙ hom (z 0) (M (z ∘ succ))
   γ (succ i) = ap h (M-prop₁ (λ n → z (succ (n +ℕ i))))
              ∙ hom (z (succ (0 +ℕ i))) (M ((λ n → z (succ (n +ℕ i))) ∘ succ))
              ∙ {!!}

 affine-M-homo : (x y : 𝕀) (z : ℕ → 𝕀) → affine x y (M z) ≡ M (λ n → affine x y (z n))
 affine-M-homo x y z = hom→hom (affine x y) (affine-is-midpoint-hom x y) z

\end{code}

  * Adopt convention u = -1 and v = 1 for the following.

  * Definability of 1 - x and xy (multiplication) (page 19 uses the
    convention u = 0 and v = 1 so we should use page 24).

\begin{code}

 ₋₁ ₀₀ ₊₁ : 𝕀
 ₋₁ = u
 ₊₁ = v
 ₀₀  = ₋₁ ⊕ ₊₁

 −_ : 𝕀 → 𝕀
 − x = affine ₊₁ ₋₁ x

 −-prop₁ : (− ₋₁) ≡ ₊₁
 −-prop₁ = affine-equation-l ₊₁ ₋₁

 −-prop₂ : (− ₊₁) ≡ ₋₁
 −-prop₂ = affine-equation-r ₊₁ ₋₁

 negation-involutive : (x : 𝕀) → affine u v x ≡ − (− x)
 negation-involutive = affine-uniqueness· ((λ x → − (− x))) u v {!!} {!!} {!!}
 -- (λ x → − (− x)) u v {!!} {!!} {!!}

 mul : 𝕀 → 𝕀 → 𝕀
 mul x y = affine (− x) x y

 mul-prop₁ : (y : 𝕀) → mul ₋₁ y ≡ − y
 mul-prop₁ y = ap (λ - → affine - ₋₁ y) −-prop₁

 mul-prop₂ : (y : 𝕀) → mul ₊₁ y ≡ y
 mul-prop₂ y = ap (λ - → affine - ₊₁ y) −-prop₂ ∙ {!!} -- h-prop₄ y

 infixl 10 _*_

 *-comm : (x y : 𝕀) → mul x y ≡ mul y x
 *-comm x = γ
  where
   i : is-homomorphism 𝓘 𝓘 (λ y → mul y x)
   i y z = p
    where
     p : mul (y ⊕ z) x ≡ (mul y x ⊕ mul z x)
     p = affine-uniqueness· (λ x → mul y x ⊕ mul z x) (− (y ⊕ z)) (y ⊕ z) {!!} {!!} {!!} {!!}
   γ : mul x ∼ (λ y → mul y x)
   γ = affine-uniqueness· (λ y → mul y x) (− x) x {!!} {!!} {!!}

 *-commu2 : (x y : 𝕀) → mul x u ≡ mul u x
 *-commu2 x y = affine-equation-l (− x) x ∙ ap (λ - → affine - u x) (−-prop₁ ⁻¹)

 *-commu3 : (x a b : 𝕀) → mul x (a ⊕ b) ≡ mul (a ⊕ b) x
 *-commu3 x a b = γ where
   γ : affine (− x) x (a ⊕ b) ≡ affine (− (a ⊕ b)) (a ⊕ b) x
   γ = affine-is-midpoint-hom (− x) x a b
       ∙ {!!}


-- mul x y = affine (− x) x y

\end{code}

  * Medial power series (page 20 and 21).

  * Page 24: not only the definitions, but the fact that we get
    commutativity and associativity.

  * Page 25.

  * Page 35.

  * Page 42.

\begin{code}

 ⊕-assoc : (x y z : 𝕀) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
 ⊕-assoc x y z = {!!}
