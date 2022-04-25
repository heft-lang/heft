module Heft.TC.Substitution where 

import qualified Data.Map as Map
import qualified Data.Set as Set 

import Heft.Syntax.Misc
import Heft.Syntax.Type


data Substitution = Substitution
 { typeSubstitutions :: Env Type
 , rowSubstitutions  :: Env Row
 }



{- Substitutions form a monoid -} 

emptySubstitution :: Substitution
emptySubstitution = Substitution
  { typeSubstitutions = mempty
  , rowSubstitutions  = mempty
  }

appendSubstitutions :: Substitution -> Substitution -> Substitution
appendSubstitutions s1 s2 = Substitution
  { typeSubstitutions = (apply s1 <$> typeSubstitutions s2) <> typeSubstitutions s1
  , rowSubstitutions  = (apply s1 <$> rowSubstitutions  s2) <> rowSubstitutions  s1
  } 

instance Semigroup Substitution where
  (<>) = appendSubstitutions

instance Monoid Substitution where
  mempty = emptySubstitution 

-- Create a single type substitution
singT :: (String , Type) -> Substitution
singT (x , t) = Substitution
  { typeSubstitutions = Env { entries = Map.singleton x t }
  , rowSubstitutions  = mempty 
  }

singR :: (String , Row) -> Substitution
singR (x , t) = Substitution
  { typeSubstitutions = mempty 
  , rowSubstitutions  = Env { entries = Map.singleton x t } 
  }


-- Defines common operations for the (mutually recursive) syntax of types 
class TypeSyntax a where
  
  -- collect all the free type/row varaibles from a piece of syntax
  ftv :: a -> Set.Set Name
  frv :: a -> Set.Set Name

  -- Applies a substitution
  apply :: Substitution -> a -> a 

(<$$>) :: TypeSyntax a => Substitution -> a -> a 
(<$$>) = apply 

-- `Env` can be considered "type syntax", if it's entries are as well
instance TypeSyntax a => TypeSyntax (Env a) where
  ftv   = foldr Set.union mempty . fmap ftv
  frv   = foldr Set.union mempty . fmap frv 
  apply = fmap . apply


instance TypeSyntax Type where

  ftv (FunT t u)         = ftv t <> ftv u
  ftv (AppT t u)         = ftv t <> ftv u
  ftv (SusT t (r1 , r2)) = ftv t <> ftv r1 <> ftv r2
  ftv NumT               = mempty
  ftv BoolT              = mempty 
  ftv (VarT x  )         = Set.singleton x
  
  frv (FunT t u)         = frv t <> frv u
  frv (AppT t u)         = frv t <> frv u
  frv (SusT t (r1 , r2)) = frv t <> frv r1 <> frv r2
  frv NumT               = mempty
  frv BoolT              = mempty 
  frv (VarT _  )         = mempty 
  
  apply s   (FunT t u)         = FunT (apply s t) (apply s u)
  apply s   (AppT t u)         = AppT (apply s t) (apply s u)
  apply s   (SusT t (r1 , r2)) = SusT (apply s t) (apply s r1 , apply s r2) 
  apply _   NumT               = NumT
  apply _   BoolT              = BoolT 
  apply s t@(VarT x  )         = maybe t id (Map.lookup x (entries $ typeSubstitutions s)) 


instance TypeSyntax Row where

  ftv NilR        = mempty
  ftv (ConsR _ r) = ftv r
  ftv (VarR _)    = mempty 

  frv NilR        = mempty
  frv (ConsR _ r) = frv r
  frv (VarR x)    = Set.singleton x

  apply _   NilR        = NilR
  apply s   (ConsR l r) = ConsR l (apply s r)
  apply s r@(VarR x)    = maybe r id (Map.lookup x (entries $ rowSubstitutions s)) 

shadow :: String -> Substitution -> Substitution
shadow x s = Substitution
  { typeSubstitutions = Env $ x `Map.delete` (entries $ typeSubstitutions s)
  , rowSubstitutions  = Env $ x `Map.delete` (entries $ rowSubstitutions  s)
  }

instance TypeSyntax Scheme where
  ftv (Scheme ts _  t) = ftv t `Set.difference` (Set.fromList ts)
  frv (Scheme _  rs t) = frv t `Set.difference` (Set.fromList rs)
  apply s (Scheme ts rs t) = Scheme ts rs (apply (foldr shadow s (ts <> rs)) t)


numSubscript :: Int -> String
numSubscript = map ((!!) nums . read . (flip (:) $ [])) . show
  where nums = [ '₀'
               , '₁'
               , '₂'
               , '₃'
               , '₄'
               , '₅'
               , '₆'
               , '₇'
               , '₈'
               , '₉'
               ] 

rownames :: Char -> [String] -> [String]
rownames base rs =
  if
    length rs == 1
  then
    [[base]]
  else
    map ((:) base . numSubscript) (take (length rs) [0..]) 
  
-- Normalize a scheme w.r.t. alpha equivalence
normalizeAlpha :: Scheme -> Scheme
normalizeAlpha (Scheme ts rs t) =
   Scheme nts (rownames 'ρ' rs)
    (apply (Substitution
      (Env $ Map.fromList (zipWith (,) ts (map VarT nts)))
      (Env $ Map.fromList (zipWith (,) rs (map VarR (rownames 'ρ' rs))))
    ) t)
  where nts :: [String]
        nts = take (length ts) (fmap return ['a'..])

        

-- normalize a row w.r.t. alpha equivalence 
normalizeAnn :: (Row , Row) -> (Row , Row)
normalizeAnn (r1 , r2) = (s <$$> r1 , s <$$> r2)  
  where s :: Substitution
        s = Substitution
          { typeSubstitutions = mempty
          , rowSubstitutions  = Env (Map.fromList rawSubst)
          }

        rawSubst :: [(Name , Row)]
        rawSubst = zip (Set.toList $ (frv r1 `Set.union` frv r2)) (VarR <$> rownames 'ε' (Set.toList $ (frv r1 `Set.union` frv r2)))
