{-# LANGUAGE
    FlexibleContexts
  , RankNTypes
  , GADTs
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , ScopedTypeVariables
 #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.Binary
-- Copyright   :  (c) 2009 Sebastiaan Visser
-- License     :  BSD3
--
-- Maintainer  :  sfvisser@cs.uu.nl
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic Data.Binary instances.
--
--
-- You can use these generic functions to create a 'Data.Binary' instance. For
-- example, for the 'Expr' data type from the AST example from the MutliRec
-- distribution:
--
-- > import Data.Binary
-- > import Generics.MultiRec.Base
-- > import Generics.MultiRec.Binary
-- >
-- > instance Binary Expr where
-- >   put = gput AST
-- >   get = gget AST
--
-----------------------------------------------------------------------------

module Generics.MultiRec.Binary where

import Control.Applicative
import Control.Monad
import Data.Binary
import Generics.MultiRec.Base
import Generics.MultiRec.TEq

-- * Generic Data.Binary instances.

class HBinary phi f where
  hput :: (forall ix'.               phi ix' -> r ix' -> Put)         -> phi ix -> f r ix -> Put
  hget :: (forall ix'. El phi ix' => phi ix' ->          Get (r ix')) -> phi ix           -> Get (f r ix)

instance El phi xi => HBinary phi (I xi) where
  hput t _ (I x) = t proof x
  hget g _       = I <$> g proof

instance Binary a => HBinary phi (K a) where
  hput _ _ (K x) = put x
  hget _ _       = K <$> get

instance HBinary phi U where
  hput _ _ U = put ()
  hget _ _   = return U

instance (HBinary phi f, HBinary phi g) => HBinary phi (f :+: g) where
  hput t p (L x) = put True  >> hput t p x
  hput t p (R y) = put False >> hput t p y
  hget t p       = get >>= \v -> if v then L <$> hget t p else R <$> hget t p

instance (HBinary phi f, HBinary phi g) => HBinary phi (f :*: g) where
  hput t p (x :*: y) = hput t p x >> hput t p y
  hget t p           = (:*:) <$> hget t p <*> hget t p

instance (EqS phi, El phi ix, HBinary phi f) => HBinary phi (f :>: ix) where
  hput t p (Tag x) = hput t p x
  hget t p =
    case eqS (proof :: phi ix) p of
      Nothing -> error "aap"
      Just Refl -> Tag <$> hget t p

instance (Constructor c, HBinary phi f) => HBinary phi (C c f) where
  hput t p (C x) = hput t p x
  hget t p       = C <$> hget t p

-- | Generic binary 'Put'.

gput :: (Fam phi, HBinary phi (PF phi)) => phi ix -> ix -> Put
gput p = hput (\q -> gput q . unI0) p . from p

-- | Generic binary 'Get'.

gget :: (Fam phi, HBinary phi (PF phi)) => phi ix -> Get ix
gget p = to p <$> hget (fmap I0 . gget) p

