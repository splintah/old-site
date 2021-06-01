---
title: Polymorphic lambda calculus
series: "Introduction to Type Systems"
---

In the previous post, we have explored the simply typed lambda calculus (STLC), an extension of the untyped lambda calculus with simple types.
In this post, we'll take a look at the *polymorphic lambda calculus*, also called *System F*, an extension of the STLC with *polymorphism*.

<details>
<summary>Imports etc.</summary>

> module Polymorphic where
>
> import           Control.Monad   (when)
> import           Data.Either     (fromRight)
> import           Data.List       (elemIndex)
> import qualified Data.Map.Strict as Map
> import           Data.Map.Strict (Map)
> import           Data.Maybe      (fromJust)

</details>

Motivation
==========

We have seen in the previous post how to write the identity function on booleans: $\lambda x : \mathsf{Bool}. x$.
We have also seen the identity function on boolean-to-integer functions: $\lambda x : \mathsf{Bool} \rightarrow \mathsf{Int}. x$.
As you can see, these definitions are very similar: only the type of $x$ is different, but the rest of the term is the exactly same.

This is suboptimal, because it means that we have duplication: in a large codebase, we may need the identity function on booleans, on integers, on boolean-to-boolean functions, on integer-to-boolean functions, etc.
Not only is it annoying to write all those definitions, but what if we later realise we've made a mistake?[^mistake]
We have to change *all* definitions, for every type!

To prevent such needless labour, we want to use *abstraction*: we want to be able to write the identity function for *all* types, with only *one* definition.
We will therefore extend the STLC with [*(parametric) polymorphism*](https://en.wikipedia.org/wiki/Parametric_polymorphism).
The result is called the *polymorphic lambda calculus* or [*System F*](https://en.wikipedia.org/wiki/System_F).

[^mistake]:
  Making a mistake writing the identity function is perhaps a bit silly.
  But in more complex programs, such as a sorting function, this could very well happen.

Syntax
======

To incorporate polymorphism in the STLC, we add two new sorts of types:

1. *Type variables*.
   These are just like 'normal', term-level variables, but instead of ranging over values, they range over types.
   We'll write them with capital letters.
2. *Polymorphic types*.
   These are written in formal syntax as $\forall X. \tau$, where $X$ is a type variable, and $\tau$ a type.
   ($\forall$ is the mathematical symbol with the meaning 'for all'.)
   In more Haskell-like syntax, we may write `forall X. τ`.

   An example of a polymorphic type is $\mathsf{id} : \forall X. X \rightarrow X$, which is the type of a function that accepts a value of any type, and returns that value.
   (All terms with that type turn out to be equivalent to the identity function.)

The new syntax of types is thus:

$$
\begin{align*}
  \tau ::=\ & X & \text{(type variable)} \\
      \mid\ & \forall X. \tau & \text{(polymorphic type)} \\
      \mid\ & \tau \rightarrow \tau' & \text{(function type)} \\
      \mid\ & \mathsf{Bool} & \text{(boolean type)} \\
      \mid\ & \mathsf{Int} & \text{(integer type)}
\end{align*}
$$

The new AST type for types looks like this:

< data Type
<   = TyVar String
<     -- ^ Type variable
<   | TyForall String Type
<     -- ^ Polymorphic type
<   | TyFun Type Type
<     -- ^ Function type
<   | TyBool
<     -- ^ Boolean type
<   | TyInt
<     -- ^ Integer type
<   deriving (Show, Eq)

Having updated the syntax of types, we also need to update the syntax of terms: we need terms that introduce and interact with polymorphic types.
These are the terms we add:

1. *Type abstractions*.
   Type abstractions are just like normal abstractions, but instead of introducing a variable that ranges over values, it introduces a type variable that ranges over types.

   We write type abstractions with an uppercase lambda, to distinguish them from normal abstractions: $\Lambda X. t$ for a type variable $X$ and a term $t$.
   In Haskell-like syntax, we write: `/\X. t`.

   Using type abstractions, we can write the generic identity function for which we've seen the type above: $\mathsf{id} = \Lambda X. \lambda x : X. x$.
   In the right-hand side of the type abstraction, after the period, we now can refer to $X$, but only in types.
   So we can create an abstraction that accepts a parameter of type $X$.
2. *Type applications*.
   Type applications are used to *instantiate* a term with a specific type.
   If we want to use the identity function on an integer, we need to indicate that the type variable $X$ in the definition of $\mathsf{id}$ should be replaced by $\mathsf{Int}$.

   In formal syntax, type applications are generally written the same as normal applications: $\mathsf{id}\ \mathsf{Int}$.
   But to be more explicit, we can use the Haskell syntax[^TypeApplications]: `id @Int`.

[^TypeApplications]:
  With the [`TypeApplications` extension](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#extension-TypeApplications).

We add the following to the syntax of terms:

$$
\begin{align*}
  t ::=\ & \ldots \\
   \mid\ & \Lambda X. t & \text{(type abstraction)} \\
   \mid\ & t\ \tau & \text{(type application)}
\end{align*}
$$

The updated AST for terms:

< data Term
<   = TmTyAbs String Term
<     -- ^ Type abstraction
<   | TmTyApp Term Type
<     -- ^ Type application

The rest of the AST is exactly the same as in the STLC, but you can still see it by clicking:

<details>
<summary>The rest of the AST definition</summary>

<   | TmTrue
<     -- ^ True value
<   | TmFalse
<     -- ^ False value
<   | TmInt Integer
<     -- ^ Integer value
<   | TmVar String
<     -- ^ Variable
<   | TmAbs String Type Term
<     -- ^ Lambda abstraction
<   | TmApp Term Term
<     -- ^ Application
<   | TmAdd Term Term
<     -- ^ Addition
<   | TmIf Term Term Term
<     -- ^ If-then-else conditional
<   deriving (Show, Eq)

</details>

Examples
--------

Let's look at some examples.[^no-types]
We've already seen the polymorphic identity function:

[^no-types]:
  You might notice that I don't specify the types of these examples, i.e., I don't write `tmId :: Term`.
  I haven't forgotten them, but I purposefully omitted them.
  You'll later see why.

> tmId = TmTyAbs "X" (TmAbs "x" (TyVar "X") (TmVar "x"))

And its type:

> tyId = TyForall "X" (TyFun (TyVar "X") (TyVar "X"))

We can also write the $\mathsf{const}$ function, which returns its first parameter and ignores its second: $\mathsf{const} = \Lambda A. \Lambda B. \lambda a : A. \lambda b : B. a$.
In the Haskell AST:

> tmConst = TmTyAbs "A" (TmTyAbs "B" (TmAbs "a" (TyVar "A") (TmAbs "b" (TyVar "B") (TmVar "a"))))

And its type, $\mathsf{const} : \forall A. \forall B. A \rightarrow B \rightarrow A$:

> tyConst = TyForall "A" (TyForall "B" (TyFun (TyVar "A") (TyFun (TyVar "B") (TyVar "A"))))

And we can try to use $\mathsf{const}$ to return a value.
The term $\mathsf{const}\ \mathsf{Bool}\ \mathsf{Int}\ \mathsf{False}\ 5$ should evaluate to $\mathsf{False}$, so its type should be $\mathsf{Bool}$:

> tmConstFalse5 = TmApp (TmApp (TmTyApp (TmTyApp tmConst TyBool) TyInt) TmFalse) (TmInt 5)
>
> tyConstFalse5 = TyBool

Now we understand the syntax, we can move on to type checking.

Type checking
=============

Describing the type checking of the polymorphic lambda calculus isn't actually that difficult.
We will only add two typing rules: one for type abstractions and one for type applications.
The rest of the rules will be exactly the same as those of the STLC.

The first rule we add is the one for type abstractions:

$$
  \text{T-TyAbs: } \frac{
    \Gamma \vdash t : \tau
  }{
    \Gamma \vdash \Lambda X. t : \forall X. \tau
  }
$$

This rule is quite simple: if $t$ has type $\tau$, then $\Lambda X. t$ has type $\forall X. \tau$.
This is the introduction rule for polymorphic types, since it is the only typing rule that 'produces' a $\forall$.

The rule for type applications is the elimination rule for polymorphic types: it 'removes' a $\forall$.
The rule is:

$$
  \text{T-TyApp: } \frac{
    \Gamma \vdash t : \forall X. \tau
  }{
    \Gamma \vdash t\ \tau' : \tau[X := \tau']
  }
$$

This rule says: if $t$ has type $\forall X. \tau$, then $t\ \tau'$ ($t$ applied to type $\tau'$) has type $\tau[X := \tau']$.
This type is the result of a *substitution*;
$\tau[X := \tau']$ means: substitute every free type variable $X$ in $\tau$ with $\tau'$.
But, as we will see, that's easier said than done...

First, let's look at some examples of substitution:

$$
\begin{align*}
  X[X := \mathsf{Int}] & \rightarrow \mathsf{Int} \\
  (X \rightarrow X)[X := \mathsf{Bool}] & \rightarrow (\mathsf{Bool} \rightarrow \mathsf{Bool}) \\
  (X \rightarrow Y)[X := \mathsf{Int} \rightarrow \mathsf{Bool}] & \rightarrow ((\mathsf{Int} \rightarrow \mathsf{Bool}) \rightarrow Y) \\
  (X \rightarrow (\forall X. X))[X := Y] & \rightarrow (Y \rightarrow (\forall X. X))
\end{align*}
$$

Naïve substitution
------------------

We'll try to write a function that performs a substitution.
We write `subst x ty' ty` for $\mathit{ty}[x := \mathit{ty'}]$:

< subst :: String -> Type -> Type -> Type

Defining `subst` for the simple types is easy, because they do not contain any free variables.

< subst x ty' TyBool = TyBool
< subst x ty' TyInt  = TyInt

Applying a substitution to a function type is also not that difficult: we'll just apply the substitution to the source and to the target type:

< subst x ty' (TyFun ty1 ty2) = TyFun (subst x ty' ty1) (subst x ty' ty2)

When we come across a type variable `y`, we should replace it with `ty'` if `x` is equal to `y`.
Otherwise, we keep `y`:

< subst x ty' (TyVar y)
<   | x == y    = ty'
<   | otherwise = TyVar y

When we apply the substitution to a polymorphic type, we need to be careful: we only want to apply the substitution to *free* variables, and the $\forall$ binds the variables next to it.
So only if the type abstraction binds a variable with a name different from `x`, we should apply the substitution to the right-hand side of the polymorphic type:

< subst x ty' (TyForall y ty)
<   | x == y    = TyForall y ty
<   | otherwise = TyForall y (subst x ty' ty)

Let's check some examples.
Applying a substitution on simple types should do nothing:

< subst "X" (TyFun TyBool TyInt) TyInt
<   => TyInt
<
< subst "X" (TyFun TyBool TyInt) TyBool
<   => TyBool

If we apply this substitution to the type variable `"X"`, it should be replaced:

< subst "X" (TyFun TyBool TyInt) (TyVar "X")
<   => TyFun TyBool TyInt

But if we apply it to `"Y"`, it should not be replaced:

< subst "X" (TyFun TyBool TyInt) (TyVar "Y")
<   => TyVar "Y"

The substitution should only happen on polymorphic types when `"X"` is not bound:

< subst "X" (TyFun TyBool TyInt)
<   (TyForall "Y" (TyFun (TyVar "Y") (TyVar "X")))
<     => TyForall "Y" (TyFun (TyVar "Y") (TyFun TyBool TyInt))
<
< subst "X" (TyFun TyBool TyInt)
<   (TyForall "X" (TyFun (TyVar "Y") (TyVar "X")))
<     => TyForall "X" (TyFun (TyVar "Y") (TyVar "X"))

Looks good, right?

Implementing the type checker for the added terms is now very easy:

< typeOf ctx (TmTyAbs x t) = TyForall x <$> typeOf ctx t
<
< typeOf ctx (TmTyApp t1 ty2) = do
<   ty1 <- typeOf ctx t1
<   case ty1 of
<     TyForall x ty12 -> Right $ subst x ty2 ty12
<     _ -> Left $ TypeApplicationNonPolymorphic t1 ty1

The rest of the type checker is exactly the same as the type checker for the STLC, which we've developed in the previous post.
You can still see it here:

<details>
<summary>The rest of `typeOf`</summary>

< typeOf ctx TmTrue    = Right TyBool
< typeOf ctx TmFalse   = Right TyBool
< typeOf ctx (TmInt n) = Right TyInt
< typeOf ctx (TmVar x) =
<   case Map.lookup x ctx of
<     Nothing -> Left $ UnboundVariable x
<     Just ty -> Right ty
< typeOf ctx (TmAbs x ty t) =
<   let ctx' = Map.insert x ty ctx
<       ty'  = typeOf ctx' t
<    in TyFun ty <$> ty'
< typeOf ctx (TmApp t1 t2) = do
<   ty1 <- typeOf ctx t1
<   ty2 <- typeOf ctx t2
<   case ty1 of
<     TyFun ty11 ty12 ->
<       if ty2 == ty11
<         then Right ty12
<         else Left $ ApplicationWrongArgumentType t1 ty1 t2 ty2
<     _ -> Left $ ApplicationNotFunction t1 ty1
< typeOf ctx (TmAdd t1 t2) = do
<   ty1 <- typeOf ctx t1
<   when (ty1 /= TyInt) $
<     Left $ AdditionNonInteger t1 ty1
<   ty2 <- typeOf ctx t2
<   when (ty2 /= TyInt) $
<     Left $ AdditionNonInteger t2 ty2
<   Right TyInt
< typeOf ctx (TmIf t1 t2 t3) = do
<   ty1 <- typeOf ctx t1
<   when (ty1 /= TyBool) $
<     Left $ NonBooleanCondition t1 ty1
<   ty2 <- typeOf ctx t2
<   ty3 <- typeOf ctx t3
<   when (ty2 /= ty3) $
<     Left $ ArmsOfDifferentType t2 ty2 t3 ty3
<   Right ty2

And the other necessary definitions:

< typeOf :: Context -> Term -> Either TypeError Type
<
< data TypeError
<   = UnboundVariable String
<   | AdditionNonInteger Term Type
<   | NonBooleanCondition Term Type
<   | ArmsOfDifferentType Term Type Term Type
<   | ApplicationWrongArgumentType Term Type Term Type
<   | ApplicationNotFunction Term Type
<   | TypeApplicationNonPolymorphic Term Type
<   deriving (Show, Eq)
<
< type Context = Map String Type

</details>

We can try some examples:

< typeOf Map.empty tmId
<   => Right (TyForall "X" (TyFun (TyVar "X") (TyVar "X")))
<
< typeOf Map.empty tmId == Right tyId
<  => True
<
< typeOf Map.empty tmConst
<   => Right
<        (TyForall "A" (TyForall "B"
<         (TyFun
<          (TyVar "A")
<          (TyFun (TyVar "B") (TyVar "A")))))
<
< typeOf Map.empty tmConst == Right tyConst
<   => True
<
< typeOf Map.empty tmConstFalse5
<   => Right TyBool
<
< typeOf Map.empty tmConstFalse5 == Right tyConstFalse5
<   => True

Looks pretty good, doesn't it?
But there's a sneaky problem, and it has to do with our definition of `subst`.[^other-problem]

[^other-problem]:
  There is also another problem: the definition of `(==)` for types isn't correct.
  We will later fix that problem.

Let's say we want to write a function that flips the type arguments of $\mathsf{const}$, so $\Lambda A. \Lambda B. \lambda a : A. \lambda b : B. a$ should become $\Lambda A. \Lambda B. \lambda a : B. \lambda b : A. a$.
And we're going to write it using the definition of $\mathsf{const}$ we've already written.
Writing this function is quite easy: $\mathsf{constFlip} = \Lambda A. \Lambda B. \mathsf{const}\ B\ A$.

The type of $\mathsf{const}$ is $\forall A. \forall B. A \rightarrow B \rightarrow A$, so what should the type of $\mathsf{constFlip}$ be?
Well, that should be $\forall A. \forall B. B \rightarrow A \rightarrow B$, right?
Let's ask our type checker:

> tmConstFlip = TmTyAbs "A" (TmTyAbs "B" (TmTyApp (TmTyApp tmConst (TyVar "B")) (TyVar "A")))

< typeOf Map.empty tmConstFlip
<   => Right (TyForall "A" (TyForall "B" (TyFun (TyVar "A") (TyFun (TyVar "A") (TyVar "A")))))

Let's make that a bit nicer to read: our type checker says that $\mathsf{constFlip}$ has type $\forall A. \forall B. A \rightarrow A \rightarrow A$.

What‽
That's not right!
We have lost all our $B$'s!

Indeed, we've made a mistake, namely in our definition of `subst`.
Let's look at the type checking process of $\mathsf{constFlip}$.
The first step is:

$$
  \text{T-TyApp: } \frac{
    \Gamma \vdash \mathsf{const} : \forall A. \forall B. A \rightarrow B \rightarrow A
  }{
    \Gamma \vdash \mathsf{const}\ B : (\forall B. A \rightarrow B \rightarrow A)[A := B]
  }
$$

Applying the substitution with our definition of `subst` gives: $\forall B. B \rightarrow B \rightarrow B$.
Note that the $B$'s that were first $A$'s are now *captured* by the $\forall B$, which means that they now refer to something they shouldn't refer to!

The next step:

$$
  \text{T-TyApp: } \frac{
    \Gamma \vdash \mathsf{const}\ B : \forall B. B \rightarrow B \rightarrow B
  }{
    \Gamma \vdash \mathsf{const}\ B\ A : (B \rightarrow B \rightarrow B)[B := A]
  }
$$

Applying this substitution gives: $A \rightarrow A \rightarrow A$.
In the following steps, the quantifiers are added back, so our end result is: $\forall B. \forall A. A \rightarrow A \rightarrow A$.

The problem we run into here, is that we should rename some type variables.
We can, for example, write $\mathsf{const}$ as $\Lambda C. \Lambda D. \lambda a : C. \lambda b : D. a$.
The type is then $\forall C. \forall D. C \rightarrow D \rightarrow C$.
Now, if we type check $\mathsf{constFlip}$, we get the right result:

> tmConst' = TmTyAbs "C" (TmTyAbs "D" (TmAbs "a" (TyVar "C") (TmAbs "b" (TyVar "D") (TmVar "a"))))
>
> tmConstFlip' = TmTyAbs "A" (TmTyAbs "B" (TmTyApp (TmTyApp tmConst' (TyVar "B")) (TyVar "A")))

< typeOf Map.empty tmConstFlip'
<   => Right (TyForall "A" (TyForall "B" (TyFun (TyVar "B") (TyFun (TyVar "A") (TyVar "B")))))

That is $\forall A. \forall B. B \rightarrow A \rightarrow B$, exactly what we wanted.

To solve this problem, we should let our `subst` function rename some type variables to *fresh* (i.e., not already used) variables.
This isn't *very* hard to implement, but there is a nicer solution that is easier to reason about.

De Bruijn-indices
=================

We will use [*De Bruijn-indices*](https://en.wikipedia.org/wiki/De_Bruijn_index).
These indices will replace our type variable names, for which we used strings.
Instead, we'll use integers.
The integer $n$ will refer to the $n$th binding $\forall$, counting outwards from the variable and starting from zero[^zero-one].
So the type for $\mathsf{const}$, which is $\forall A. \forall B. A \rightarrow B \rightarrow A$, will be written as $\forall. \forall. 1 \rightarrow 0 \rightarrow 1$.
(We'll actually keep the bound names in the AST: $\forall A. \forall B. 1 \rightarrow 0 \rightarrow 1$, but that is not necessary.)

[^zero-one]:
  It is also common to start counting from one, but since we will use lists and their indices (which in Haskell's `Prelude` start from zero), it is more convenient to start counting from zero.

To apply these changes to the Haskell AST, we won't just change `TyVar String` into `TyVar Int`, but we'll write:

> data Type x
>   = TyVar x
>     -- ^ Type variable
>   | TyForall String (Type x)
>     -- ^ Polymorphic type
>   | TyFun (Type x) (Type x)
>     -- ^ Function type
>   | TyBool
>     -- ^ Boolean type
>   | TyInt
>     -- ^ Integer type
>   deriving (Show, Eq)

This allows us to construct the ordinary types as well as the types with De Bruijn-indices.
We choose to do this because it makes writing a parser significantly easier: the parser can return a `Type String`, and we can later turn this into a `Type Int`.
The `deBruijn` function does just that:

> deBruijn :: [String] -> Type String -> Either String (Type Int)
> deBruijn ctx (TyVar x) = case elemIndex x ctx of
>     Nothing -> Left x
>     Just i  -> Right (TyVar i)
> deBruijn ctx (TyForall x ty) = TyForall x <$> deBruijn (x : ctx) ty 
> deBruijn ctx (TyFun ty1 ty2) = TyFun <$> deBruijn ctx ty1 <*> deBruijn ctx ty2
> deBruijn ctx TyBool          = Right TyBool
> deBruijn ctx TyInt           = Right TyInt

The `deBruijn` function turns an ordinary type into a type with De Bruijn-indices.
It walks the abstract syntax tree recursively.
When it comes across a $\forall$, it adds the bound type variable to the context, which is a list of `String`s here.
When it sees a variable, it tries to find it in the context, and if it is found, it is replaced by the index of the variable in the context.
If the variable is not found in the context, we return `Left x`, to indicate that the function failed because `x` was unbound.

We can also restore the names (because we haven't removed the names that are bound by the $\forall$'s)[^restore]:

[^restore]:
  The `restore` function does not work in general, but it should work on types generated by `deBruijn`.
  An example that doesn't work: $\forall X. \forall X. 0 \rightarrow 1$.
  Both $0$ and $1$ will be replaced by $X$, and they will both refer to the inner $X$, but the $1$ should refer to the outer $X$.

> restore :: Type Int -> Maybe (Type String)
> restore = go []
>  where
>   go ctx (TyVar i)       = TyVar <$> nth i ctx
>   go ctx (TyForall x ty) = TyForall x <$> go (x : ctx) ty
>   go ctx (TyFun ty1 ty2) = TyFun <$> go ctx ty1 <*> go ctx ty2
>   go ctx TyBool          = Just TyBool
>   go ctx TyInt           = Just TyInt
>
>   -- Get the @n@th element of a list, or 'Nothing'
>   -- if the length of the list is smaller than @n@.
>   -- As far as I can see, there is no such function
>   -- in base.
>   nth :: Int -> [a] -> Maybe a
>   nth n []     = Nothing
>   nth 0 (x:_)  = Just x
>   nth n (x:xs) = nth (n - 1) xs

Having changed `Type`, we also need to change `Term`, since terms can contain types.
Doing this is very straight-forward and quite boring, but you can view the new definition here:

<details>
<summary>The updated `Term x`</summary>

> data Term x
>   = TmTyAbs String (Term x)
>     -- ^ Type abstraction
>   | TmTyApp (Term x) (Type x)
>     -- ^ Type application
>   | TmTrue
>     -- ^ True value
>   | TmFalse
>     -- ^ False value
>   | TmInt Integer
>     -- ^ Integer value
>   | TmVar String
>     -- ^ Variable
>   | TmAbs String (Type x) (Term x)
>     -- ^ Lambda abstraction
>   | TmApp (Term x) (Term x)
>     -- ^ Application
>   | TmAdd (Term x) (Term x)
>     -- ^ Addition
>   | TmIf (Term x) (Term x) (Term x)
>     -- ^ If-then-else conditional
>   deriving (Show, Eq)

</details>

The substitution function for types with De Bruijn-indices is as follows:

> subst :: Int -> Type Int -> Type Int -> Type Int

The simple types are again very simple:
  
> subst x ty' TyBool = TyBool
> subst x ty' TyInt  = TyInt

For function types, we just apply the substitution left and right:
  
> subst x ty' (TyFun ty1 ty2) =
>   TyFun (subst x ty' ty1) (subst x ty' ty2)

When we see a variable, we only substitute it if `x` equals `y`:
  
> subst x ty' (TyVar y)
>   | x == y    = ty'
>   | otherwise = TyVar y

And here is the tricky bit.
A $\forall$ binds a type variable, so to make `x` still refer to the same $\forall$ it was bound by, we need to increment it by one.
But we also need to shift all free type variables in `ty'` by one, because they will otherwise be bound by a different $\forall$.
(This was the problem we ran into before and can solve using De Bruijn-indices.)

> subst x ty' (TyForall y ty) =
>   TyForall y $ subst (x + 1) (shift 0 1 ty') ty

Let's look at the substitution $(\forall X. 0_X \rightarrow 2_Z)[1_Z := 0_Y]$.
We're working in a context $Z, Y$ so the term $Z\ Y$ should be written like $1_Z\ 0_Y$.
(I've added subscripts with the names to make the terms easier to read.)
When we see the $\forall X. \ldots$, another name is bound, so $1$ no longer refers to $Z$ but to $Y$, and $0$ no longer refers to $Y$ but to $X$.
We need to shift $1_Z$ by one, so it becomes $2_Z$, and we need to shift $0_Y$ by one, so it becomes $1_Y$.
The above substitution is then equal to $\forall X. (0_X \rightarrow 2_Z)[2_Z := 1_Y]$.
For this substitution, we don't need to do any shifting, so the result is $\forall X. 0_X \rightarrow 1_Y$.

It becomes more complicated when we want to substitute for a polymorphic type that binds some type variables.
Let's say we're working in the context $Y, B$ and we want to evaluate $(\forall A. A \rightarrow B)[B := \forall X. X \rightarrow Y]$.
In De Bruijn-indices, this is: $(\forall A. 0_A \rightarrow 1_B)[0_B := \forall X. 0_X \rightarrow 2_Y]$.
We see $\forall A. \ldots$, so we need to shift the variables in the substitution up by one.
Naïvely, we would just increment all type variables by one, so we get: $\ldots[1 := \forall X. 1 \rightarrow 3]$.
I've deliberately not written the subscripts, because they have changed.
The $0_X$ has become a $1_B$, so the substitution has become a different one.

To solve this, we need to keep track of a *cutoff* ($c$).
This value denotes the 'depth' of the type, that is, how many type variables are bound by $\forall$'s.
The function `shift c i ty` will shift the free type variables above a cutoff `c` by `i`:

> shift :: Int -> Int -> Type Int -> Type Int

There are no free variables in the simple types, so there is nothing to shift:
  
> shift c i TyBool = TyBool
> shift c i TyInt  = TyInt

We shift function types by just shifting recursively:
  
> shift c i (TyFun ty1 ty2) =
>   TyFun (shift c i ty1) (shift c i ty2)

When we see a $\forall$, we need to increase the cutoff, since there is another bound variable introduced:
  
> shift c i (TyForall x ty) =
>   TyForall x $ shift (c + 1) i ty

And finally,  when we come across a variable, we should only shift it when it's free (and thus not bound).
That is the case when the variable is greater than or equal to the cutoff:
  
> shift c i (TyVar x) =
>   if x < c
>    then TyVar x
>    else TyVar (x + i)

Some examples:

< shift 0 1 (TyForall "X"
<            (TyFun (TyVar 0 {- bound: X -})
<                   (TyVar 1 {- free -})))
<   => TyForall "X" (TyFun (TyVar 0) (TyVar 2))
<
< shift 0 1 (TyForall "X" (TyForall "Y"
<            (TyFun (TyVar 0 {- bound: X -})
<                   (TyVar 1 {- bound: Y -}))))
<   => TyForall "X" (TyForall "Y" (TyFun (TyVar 0) (TyVar 1)))

And let's try the substitutions we've seen above.
$(\forall X. 0_X \rightarrow 2_Z)[1_Z := 0_Y]$:

< subst 1 (TyVar 0) (TyForall "X" (TyFun (TyVar 0) (TyVar 2)))
<   => TyForall "X" (TyFun (TyVar 0) (TyVar 1))

That is: $\forall X. 0_X \rightarrow 1_Y$.

And $(\forall A. 0_A \rightarrow 1_B)[0_B := \forall X. 0_X \rightarrow 2_Y]$:

< subst 0 (TyForall "X" (TyFun (TyVar 0) (TyVar 2))) (TyForall "A" (TyFun (TyVar 0) (TyVar 1)))
<   => TyForall "A" (TyFun (TyVar 0) (TyForall "X" (TyFun (TyVar 0) (TyVar 3))))

That is: $\forall A. 0_A \rightarrow (\forall X. 0_X \rightarrow 3_Y)$.

Type checking, again
====================

Now we have written our definition of substitutions, we can *almost* move on to implementing the type checker.
But first, we need to turn the `Term String`s into `Term Int`s.
Note that we only use De Bruijn-indices for types, so terms still use variables with a string name:

> deBruijnTerm :: [String] -> Term String -> Either String (Term Int)
> deBruijnTerm ctx TmTrue = Right TmTrue
> deBruijnTerm ctx TmFalse = Right TmFalse
> deBruijnTerm ctx (TmInt n) = Right (TmInt n)
> deBruijnTerm ctx (TmVar x) = Right (TmVar x)

Type abstractions introduce a type variable, so we should add it to the context:
  
> deBruijnTerm ctx (TmTyAbs x t) = TmTyAbs x <$> deBruijnTerm (x : ctx) t
> deBruijnTerm ctx (TmTyApp t ty) = TmTyApp <$> deBruijnTerm ctx t <*> deBruijn ctx ty
> deBruijnTerm ctx (TmAbs x ty t) = TmAbs x <$> deBruijn ctx ty <*> deBruijnTerm ctx t
> deBruijnTerm ctx (TmApp t1 t2) = TmApp <$> deBruijnTerm ctx t1 <*> deBruijnTerm ctx t2
> deBruijnTerm ctx (TmAdd t1 t2) = TmAdd <$> deBruijnTerm ctx t1 <*> deBruijnTerm ctx t2
> deBruijnTerm ctx (TmIf t1 t2 t3) = TmIf <$> deBruijnTerm ctx t1 <*> deBruijnTerm ctx t2 <*> deBruijnTerm ctx t3

Some examples:

< deBruijnTerm [] tmId
<   => Right (TmTyAbs "X" (TmAbs "x" (TyVar 0) (TmVar "x")))
<
< deBruijnTerm [] tmConst
<   => Right (TmTyAbs "A" (TmTyAbs "B" (TmAbs "a" (TyVar 1) (TmAbs "b" (TyVar 0) (TmVar "a")))))
<
< deBruijnTerm [] tmConstFlip
<   => Right (TmTyAbs "A" (TmTyAbs "B" (TmTyApp (TmTyApp (TmTyAbs "A" (TmTyAbs "B" (TmAbs "a" (TyVar 1) (TmAbs "b" (TyVar 0) (TmVar "a"))))) (TyVar 0)) (TyVar 1))))

Now we can implement the type checker:

> type Context = Map String (Type Int)
>
> typeOf :: Context -> Term Int -> Either (TypeError Int) (Type Int)

<details>
<summary>The definition of `TypeError`</summary>
 
> data TypeError x

The variable was not bound by a lambda abstraction.
  
>   = UnboundVariable String

An operand of an addition term was not an integer.

>   | AdditionNonInteger (Term x) (Type x)

The condition of an if-then-else term is not a boolean.
  
>   | NonBooleanCondition (Term x) (Type x)

The arms of an if-then-else term have different types.
    
>   | ArmsOfDifferentType (Term x) (Type x) (Term x) (Type x)

A function is applied to an argument of the wrong type.

>   | ApplicationWrongArgumentType (Term x) (Type x) (Term x) (Type x)

A term of a non-function type is the left part of an application.

>   | ApplicationNotFunction (Term x) (Type x)

A type is applied to a term with a non-polymorphic type.

>   | TypeApplicationNonPolymorphic (Term x) (Type x)
>   deriving (Show)

</details>

Type checking a type abstraction is still pretty simple:

> typeOf ctx (TmTyAbs x t) = TyForall x <$> typeOf ctx t

But type checking a type application is a bit more involved.
We don't just apply the substitution, but do some shifting around it.
With the pattern matching, we assert that `ty1` is of the form $\forall X. \mathsf{ty12}$ for some type variable $X$ and some type $\mathsf{ty12}$.
We need to shift $\mathsf{ty2}$ up, because its context is one smaller than the context of $\mathsf{ty12}$.
And we need to shift $\mathsf{ty12}$ one down after the substitution, because we have removed $X$ from the context by pattern matching on `ty1`:
  
> typeOf ctx (TmTyApp t1 ty2) = do
>   ty1 <- typeOf ctx t1
>   case ty1 of
>     TyForall x ty12 -> Right $
>       shift 0 (-1) (subst 0 (shift 0 1 ty2) ty12)
>     _ -> Left $ TypeApplicationNonPolymorphic t1 ty1

Most of `typeOf` is still the same:

<details>
<summary>Most of `typeOf`</summary>

> typeOf ctx TmTrue    = Right TyBool
> typeOf ctx TmFalse   = Right TyBool
> typeOf ctx (TmInt n) = Right TyInt
> typeOf ctx (TmVar x) =
>   case Map.lookup x ctx of
>     Nothing -> Left $ UnboundVariable x
>     Just ty -> Right ty
> typeOf ctx (TmAbs x ty t) =
>   let ctx' = Map.insert x ty ctx
>       ty'  = typeOf ctx' t
>    in TyFun ty <$> ty'
> typeOf ctx (TmAdd t1 t2) = do
>   ty1 <- typeOf ctx t1
>   when (ty1 /= TyInt) $
>     Left $ AdditionNonInteger t1 ty1
>   ty2 <- typeOf ctx t2
>   when (ty2 /= TyInt) $
>     Left $ AdditionNonInteger t2 ty2
>   Right TyInt

</details>

But we also have to update how we type check normal applications and if-then-else terms.
To check whether the argument type matches the parameter type of the left-hand side, we test whether they are equal.
Similarly, for if-then-else terms we check whether the types of the arms are equal.
But the `Eq` instance for `Type`s is derived, so two polymorphic types `TyForall x ty1` and `TyForall y ty2` are equal if and only if `x == y` and `ty1 == ty2`.
But $\forall X. 0_X$ and $\forall Y. 0_Y$ are clearly the same type.
So we can just ignore the first parameter of `TyForall` when comparing them since we are using De Bruijn-indices which don't have to be renamed.
We'll use the `tyEq` function for testing whether two types are equal[^Eq-Int-Bool]:

[^Eq-Int-Bool]:
  Testing whether a type is equal to `TyBool` or `TyInt` can still be done using `(==)`.

> typeOf ctx (TmApp t1 t2) = do
>   ty1 <- typeOf ctx t1
>   ty2 <- typeOf ctx t2
>   case ty1 of
>     TyFun ty11 ty12 ->
>       if tyEq ty2 ty11
>         then Right ty12
>         else Left $ ApplicationWrongArgumentType t1 ty1 t2 ty2
>     _ -> Left $ ApplicationNotFunction t1 ty1
>
> typeOf ctx (TmIf t1 t2 t3) = do
>   ty1 <- typeOf ctx t1
>   when (ty1 /= TyBool) $
>     Left $ NonBooleanCondition t1 ty1
>   ty2 <- typeOf ctx t2
>   ty3 <- typeOf ctx t3
>   when (not (tyEq ty2 ty3)) $
>     Left $ ArmsOfDifferentType t2 ty2 t3 ty3
>   Right ty2
>
> tyEq :: Type Int -> Type Int -> Bool
> tyEq (TyVar x) (TyVar y)                 = x == y
> tyEq (TyForall _ ty1) (TyForall _ ty2)   = tyEq ty1 ty2
> tyEq (TyFun ty11 ty12) (TyFun ty21 ty22) = tyEq ty11 ty21 && tyEq ty12 ty22
> tyEq TyBool TyBool                       = True
> tyEq TyInt TyInt                         = True
> tyEq _ _                                 = False

And with that, we should have a working type checker for the polymorphic lambda calculus!
Let's try it:

< let Right tmConstDB = deBruijnTerm [] tmConst
<  in typeOf Map.empty tmConstDB
<   => Right (TyForall "A" (TyForall "B" (TyFun (TyVar 1) (TyFun (TyVar 0) (TyVar 1)))))

We can also `restore` the term:

< let Right tmDB = deBruijnTerm [] tmConst
<     Right ty   = typeOf Map.empty tmDB
<  in restore ty
<   => Just (TyForall "A" (TyForall "B"
<            (TyFun (TyVar "A")
<                   (TyFun (TyVar "B")
<                          (TyVar "A")))))

$\mathsf{const} : \forall A. \forall B. A \rightarrow B \rightarrow A$, just what we expected!

Now let's try $\mathsf{constFlip}$, which failed previously:

< let Right tmDB = deBruijnTerm [] tmConstFlip
<     Right ty   = typeOf Map.empty tmDB
<  in restore ty
<   => Just (TyForall "A" (TyForall "B"
<            (TyFun (TyVar "B")
<                   (TyFun (TyVar "A")
<                          (TyVar "B")))))

$\mathsf{constFlip} : \forall A. \forall B. B \rightarrow A \rightarrow B$, hurray!

And let's also check that we can apply polymorphic functions, $(\lambda \mathsf{id} : (\forall X. X \rightarrow X). \mathsf{id}\ \mathsf{Int}\ 6)\ (\Lambda Y. \lambda y : Y. y)$:

< let tm = TmApp
<            (TmAbs "id" (TyForall "X" (TyFun (TyVar "X") (TyVar "X")))
<              (TmApp (TmTyApp (TmVar "id") TyInt) (TmInt 6)))
<            (TmTyAbs "Y" (TmAbs "y" (TyVar "Y") (TmVar "y")))
<     Right tmDB = deBruijnTerm [] tm
<     Right ty = typeOf Map.empty tmDB
<  in ty
<   => TyInt

Cool!
(Writing this example, I wished I had written a parser...)

Note, however, that restoring does not always work:

< let tm = TmTyAbs "B" (TmTyApp tmConst (TyVar "B"))
<     Right tmDB = deBruijnTerm [] tm
<     Right ty = typeOf Map.empty tmDB
<  in (ty, restore ty)
<   => ( TyForall "B" (TyForall "B" (TyFun (TyVar 1) (TyFun (TyVar 0) (TyVar 1))))
<      , Just (TyForall "B" (TyForall "B" (TyFun (TyVar "B") (TyFun (TyVar "B") (TyVar "B")))))
<      )

The first type, using De Bruijn-indices, is correct: $\forall B. \forall B. 1_B \rightarrow 0_B \rightarrow 1_B$.
The second, restored type, however, is: $\forall B. \forall B. B \rightarrow B \rightarrow B$.
If we turn this into a `Type Int`, we get $\forall B. \forall B. 0_B \rightarrow 0_B \rightarrow 0_B$, which is not equal to the original.
To solve this, you would need to do some renaming.

Some more examples:

> everything :: Term String -> Type String
> everything = fromJust . restore . fromRight oops . typeOf Map.empty . fromRight oops . deBruijnTerm []
>  where
>   oops = error "everything: expected Right but found Left"

$\mathsf{id}\ \mathsf{Bool}\ \mathsf{True}$:

< everything (TmApp (TmTyApp tmId TyBool) TmTrue)
<   => TyBool

$\mathsf{const}\ \mathsf{Int}\ (\mathsf{Int} \rightarrow \mathsf{Bool})\ (10 + 20)\ (\mathsf{const}\ \mathsf{Bool}\ \mathsf{Int}\ \mathsf{False})$:

< everything (TmApp (TmApp (TmTyApp (TmTyApp tmConst TyInt) (TyFun TyInt TyBool)) (TmAdd (TmInt 10) (TmInt 20))) (TmApp (TmTyApp (TmTyApp tmConst TyBool) TyInt) TmFalse))
<   => TyInt

$(\mathbf{if}\ \mathsf{False}\ \mathbf{then}\ (\Lambda A. \lambda a : A. a)\ \mathbf{else}\ (\Lambda B. \lambda b : B. b))\ \mathsf{Int}\ 5$

< everything (TmApp (TmTyApp (TmIf TmFalse (TmTyAbs "A" (TmAbs "a" (TyVar "A" (TmVar "a")))) (TmTyAbs "B" (TmAbs "b" (TyVar "B" (TmVar "b"))))) TyInt) (TyInt 5))
<   => TyInt

Conclusion
==========

We have explored the polymorphic lambda calculus (or System F), which allows for more abstraction than the simply typed lambda calculus.
We have met the trouble of substitution, and we have seen how we can solve it using De Bruijn-indices.

Most [exercises for the STLC](/posts/2020-05-24-Simply-typed-lambda.html#conclusion) can also be applied to the polymorphic lambda calculus.
Some other exercises:

1. Add a pair type (tuple with two elements) with a constructor (you could use $(t, t')$ if you're writing a parser; otherwise it doesn't really matter for the abstract syntax tree) and `fst` and `snd` to project elements out of the pair.
  Write the typing rules and extend the type checker.
2. Write a `restore` function that works on all types with De Bruijn-indices.
  You would need to keep track of the context, i.e., what type variables are used.
  And you need to be able to generate fresh type variables; you can try to add primes (`'`) to the first parameter of `TyForall` until the name is not bound in the context, for example.

In the next post, I will explore *type inference*, which will allow us to eliminate *all* types in the syntax of terms.
No more $\mathsf{const} = \Lambda A. \Lambda B. \lambda a : A. \lambda b : B. a$, but just $\mathsf{const} = \lambda a. \lambda b. a$.
And instead of $\mathsf{const}\ \mathsf{Int}\ \mathsf{Bool}\ 19\ \mathsf{True}$, we will write just $\mathsf{const}\ 19\ \mathsf{True}$.

Further reading
---------------

If you want to read more about De Bruijn-indices, shifting and substitution, you might find the following resources useful:

- [*CS 4110 – Programming Languages and Logics Lecture #15: De Bruijn, Combinators, Encodings*](https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf)
- [*Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/), Benjamin C. Pierce, Chapter 6.

These resources are about using De Bruijn-indices in the untyped lambda calculus, but this knowledge can also be applied to types.
If you find shifting and substitution for De Bruijn-indices a bit hard to grasp (I did when I first learnt about them), I recommend you try to work out some examples by hand.
