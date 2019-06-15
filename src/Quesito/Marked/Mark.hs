module Quesito.Marked.Mark (mark, unmark) where

import Data.Tuple (swap)

import Quesito
import Quesito.TT (AttrLit(..), BinOp, UnOp)
import qualified Quesito.TT as TT
import qualified Quesito.Marked as Marked

import qualified Data.HashMap.Strict as Map

type Occ = Map.HashMap String Int

-- Term annotated with occurences in closure
data OccTerm
  = Local String
  | Meta String
  | Global String
  | BaseType Int
  | UniquenessAttr
  | AttrLit AttrLit
  | Type Int OccTerm
  | Attr OccTerm OccTerm
  | BytesType Int
  | Num Int
  | BinOp BinOp
  | UnOp UnOp
  | Pi String OccTerm OccTerm Occ
  | App OccTerm OccTerm
  | Ann OccTerm OccTerm
  | Lam String OccTerm Occ
  | Loc Location OccTerm
  deriving Show

mark :: TT.Term -> Marked.Term
mark =
  uncurry mark' . swap . buildMap Map.empty
  where
    buildMap
      :: Occ
      -> TT.Term
      -> (OccTerm, Occ)
    buildMap m (TT.Local x) =
      (Local x, Map.insertWith (+) x 1 m)
    buildMap m (TT.Meta x) =
      (Meta x, m)
    buildMap m (TT.Global x) =
      (Global x, m)
    buildMap m (TT.BaseType i) =
      (BaseType i, m)
    buildMap m TT.UniquenessAttr =
      (UniquenessAttr, m)
    buildMap m (TT.AttrLit u) =
      (AttrLit u, m)
    buildMap m (TT.Type i u) =
      let
        (u', m') = buildMap m u
      in
        (Type i u', m')
    buildMap m (TT.Attr t u) =
      let
        (t', m') = buildMap m t
        (u', m'') = buildMap m' u
      in
        (Attr t' u', m'')
    buildMap m (TT.BytesType i) =
      (BytesType i, m)
    buildMap m (TT.Num i) =
      (Num i, m)
    buildMap m (TT.BinOp op) =
      (BinOp op, m)
    buildMap m (TT.UnOp op) =
      (UnOp op, m)
    buildMap m (TT.Pi x r s) =
      let
        (r', mr) = buildMap m r
        (s', ms) = buildMap Map.empty s
      in
        (Pi x r' s' ms, Map.unionWith (+) (Map.delete x ms) mr)
    buildMap m (TT.App r s) =
      let
        (r', m') = buildMap m r
        (s', m'') = buildMap m' s
      in
        (App r' s', m'')
    buildMap m (TT.Ann e ty) =
      let
        (e', m') = buildMap m e
        (ty', m'') = buildMap m' ty
      in
        (Ann e' ty', m'')
    buildMap m (TT.Lam x e) =
      let
        (e', me) = buildMap Map.empty e
      in
        (Lam x e' me, Map.unionWith (+) (Map.delete x me) m)
    buildMap m (TT.Loc loc t) =
      let
        (t', m') = buildMap m t
      in
        (Loc loc t', m')

    mark'
      :: Occ
      -> OccTerm
      -> Marked.Term
    mark' m (Local v) =
      if m Map.! v == 1 then
        Marked.Local v UniqueAttr
      else
        Marked.Local v SharedAttr
    mark' _ (Meta v) =
      Marked.Meta v
    mark' _ (Global x) =
      Marked.Global x
    mark' _ (BaseType i) =
      Marked.BaseType i
    mark' _ UniquenessAttr =
      Marked.UniquenessAttr
    mark' _ (AttrLit u) =
      Marked.AttrLit u
    mark' m (Type i u) =
      Marked.Type i $ mark' m u
    mark' m (Attr t u) =
      Marked.Attr (mark' m t) (mark' m u)
    mark' _ (BytesType i) =
      Marked.BytesType i
    mark' _ (Num i) =
      Marked.Num i
    mark' _ (BinOp op) =
      Marked.BinOp op
    mark' _ (UnOp op) =
      Marked.UnOp op
    mark' m (Pi x r s ms) =
      Marked.Pi x (mark' m r) (mark' ms s)
    mark' m (App r s) =
      Marked.App (mark' m r) (mark' m s)
    mark' m (Ann e ty) =
      Marked.Ann (mark' m e) (mark' m ty)
    mark' m (Lam x e me) =
      Marked.Lam x (mark' (Map.unionWith (+) (Map.delete x m) me) e)
    mark' m (Loc loc t) =
      Marked.Loc loc (mark' m t)

unmark :: Marked.Term -> TT.Term
unmark (Marked.Local x _) =
  TT.Local x
unmark (Marked.Meta x) =
  TT.Meta x
unmark (Marked.Global x) =
  TT.Global x
unmark (Marked.BaseType i) =
  TT.BaseType i
unmark Marked.UniquenessAttr =
  TT.UniquenessAttr
unmark (Marked.AttrLit u) =
  TT.AttrLit u
unmark (Marked.Type i u) =
  TT.Type i (unmark u)
unmark (Marked.Attr t u) =
  TT.Attr (unmark t) (unmark u)
unmark (Marked.BytesType i) =
  TT.BytesType i
unmark (Marked.Num i) =
  TT.Num i
unmark (Marked.BinOp op) =
  TT.BinOp op
unmark (Marked.UnOp op) =
  TT.UnOp op
unmark (Marked.Pi x r s) =
  TT.Pi x (unmark r) (unmark s)
unmark (Marked.App r s) =
  TT.App (unmark r) (unmark s)
unmark (Marked.Ann e ty) =
  TT.Ann (unmark e) (unmark ty)
unmark (Marked.Lam x e) =
  TT.Lam x (unmark e)
unmark (Marked.Loc loc t) =
  TT.Loc loc (unmark t)
