{-# LANGUAGE TemplateHaskell #-}
module Data.Constraint.TH
  ( mkDict )
  where

import Data.Constraint
import Language.Haskell.TH

-- | Create a 'Dict' embodying a constraint. The function will have
--   the name 'dict_constraint_instance'.
--
--   Example:
--   > $(mkDict ''Eq ''String)
--   will generate the following code:
--   @
--     dict_Eq_String :: Dict (Eq String)
--     dict_Eq_String = Dict
--   @
mkDict :: Name -- Constraint to reify
       -> Name -- Instance type to make a dictionary for
       -> Q [Dec]
mkDict constraint inst = do
    dictSig <- sigD dictName (conT ''Dict `appT` dictType)
    dictVal <- valD (varP dictName) (normalB $ conE 'Dict) []
    return [dictSig, dictVal]
  where
    dictName = mkName $ "dict_" ++ nameBase constraint ++ "_" ++ nameBase inst
    dictType = conT constraint `appT` conT inst
