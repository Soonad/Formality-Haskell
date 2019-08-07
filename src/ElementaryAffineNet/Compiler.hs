module ElementaryAffineNet.Compiler where

import           Control.Monad (guard, unless, when)
import           Control.Monad.Trans.State.Lazy
import qualified Data.Map as M
import           Data.Maybe
import           ElementaryAffineCore.Types
import           ElementaryAffineNet 

compile :: Exp -> Exps -> Net
compile e _ = execState doCompile (Net M.empty [] [])
  where doCompile =
          do newNodeAddr <- allocNode
             termPtr <- buildNet e M.empty
             linkSlots (newNodeAddr, P) (newNodeAddr, R)
             linkSlots (newNodeAddr, L) ((toNode termPtr), (toSlot termPtr))

type Environment = M.Map Variable Port

buildNet :: Exp -> Environment -> State Net Port
buildNet (Exp _ eitherTerm exps) env = case eitherTerm of
   Left  ref  -> case M.lookup ref exps of
     Nothing      -> error "undefined reference"
     Just    rexp -> buildNet rexp env
   Right term -> buildNetRaw term exps env

buildNetRaw :: Term -> Exps -> Environment -> State Net Port

-- TODO handle edge cases
buildNetRaw v@(Var _) exps env =
  return $ env M.! (getVVar v)

buildNetRaw (Lam []     body) exps env = buildNet body env
buildNetRaw (Lam (v:vs) body) exps env = do
  newNodeAddr <- allocNode
  let env' = M.insert v (Ptr newNodeAddr L) env
  bodyNetPtr <- buildNetRaw (Lam vs body) exps env'
  linkSlots (newNodeAddr, R) ((toNode bodyNetPtr), (toSlot bodyNetPtr))
  return (Ptr newNodeAddr P)

buildNetRaw (App fun arg) exps env = do
  newNodeAddr <- allocNode
  funNetPtr <- buildNet fun env
  linkSlots (newNodeAddr, P) ((toNode funNetPtr), (toSlot funNetPtr))
  argNetPtr <- buildNet arg env
  linkSlots (newNodeAddr, L) ((toNode argNetPtr), (toSlot argNetPtr))
  return (Ptr newNodeAddr R)

buildNetRaw (Put body) exps env = buildNet body env

buildNetRaw (Dup v exp body) exps env = do
  expNetPtr <- buildNet exp env
  let env' = M.insert v expNetPtr env
  buildNet body env'
