data Expr
  = Var String
  | Fun String [Expr]

data F a
  = Forall String (Expr -> a) a
  | Pred String [Expr] a
  deriving (Functor)

data Free f a = Tip a | Stack (f (Free f a))

type Form = Free F

lift :: F a -> Form a
lift x = Stack (Tip <$> x)

forall :: String -> (Expr -> Form a) -> Form a
forall = lift . Forall

f :: Form
f = lift $ Forall "x" $ \x -> do