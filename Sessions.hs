{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Sessions where

import Data.Char
import Data.Kind

data SessionType =
    Type :!> SessionType
  | Type :?> SessionType
  | SessionType :&&: SessionType -- offer a choice, \&
  | SessionType :||: SessionType -- select an option, \oplus
  | End

infixr 5 :!>
infixr 5 :?>

type ExampleSession =
  Int :!> Char :?> Int :!> End

type family Dual (st :: SessionType) :: SessionType where
  Dual (a :!> st) = a :?> Dual st
  Dual (a :?> st) = a :!> Dual st
  Dual (st1 :&&: st2) = Dual st1 :||: Dual st2
  Dual (st1 :||: st2) = Dual st1 :&&: Dual st2
  Dual End        = End

-- continuation-based interface

data Session m (st :: SessionType) where
  Send :: a -> Session m st -> Session m (a :!> st)
  Receive :: (a -> Session m st) -> Session m (a :?> st)
  Done :: Session m End
  Lift :: m a -> (a -> Session m st) -> Session m st
  Branch :: Session m st1 -> Session m st2 -> Session m (st1 :&&: st2)
  Sel1 :: Session m st1 -> Session m (st1 :||: st2)
  Sel2 :: Session m st2 -> Session m (st1 :||: st2)

send :: a -> Session m st -> Session m (a :!> st)
send = Send

receive :: (a -> Session m st) -> Session m (a :?> st)
receive = Receive

done :: Session m End
done = Done

lift :: m a -> (a -> Session m st) -> Session m st
lift = Lift

lift_ :: m a -> Session m st -> Session m st
lift_ m k = lift m (const k)

branch = Branch
sel1 = Sel1
sel2 = Sel2

example :: Session IO ExampleSession
example =
  send 65 $ receive $ \ c -> lift_ (print c) $ send (ord c) $ done

match :: (Dual (Dual st) ~ st, Monad m) => Session m st -> Session m (Dual st) -> m ()
match Done Done = return ()
match (Send a1 k1) (Receive k2) = match k1 (k2 a1)
-- match (Receive k1) (Send a2 k2) = match (k1 a2) k2
match (Lift m1 k1) s2 = m1 >>= \ a -> match (k1 a) s2
-- match s1 (Lift m2 k2) = m2 >>= \ a -> match s1 (k2 a)
match (Branch k1 _) (Sel1 k2) = match k1 k2
match (Branch _ k1) (Sel2 k2) = match k1 k2
-- match (Sel1 k1) (Branch k2 _) = match k1 k2
-- match (Sel2 k1) (Branch _ k2) = match k1 k2
match s1 s2 = match s2 s1

example' :: Session IO (Dual ExampleSession)
example' =
  receive $ \ i ->
  send (chr i) $
  receive $ \ j ->
  lift_ (print (i == j)) $
  done

class HasTerminal (st :: SessionType) where
  terminal :: Session IO st

instance HasTerminal End where
  terminal = done

instance (Read a, HasTerminal st) => HasTerminal (a :!> st) where
  terminal =
    lift readLn $ \ a -> send a terminal

instance (Show a, HasTerminal st) => HasTerminal (a :?> st) where
  terminal =
    receive $ \ a -> lift_ (print a) $ terminal

instance (HasTerminal st1, HasTerminal st2) => HasTerminal (st1 :&&: st2) where
  terminal =
    branch terminal terminal

instance (HasTerminal st1, HasTerminal st2) => HasTerminal (st1 :||: st2) where
  terminal =
    lift_ (putStr "<Bool>") $ lift readLn $ \ a ->
    if a then sel1 terminal else sel2 terminal

server =
  branch
    (receive $ \ i1 -> receive $ \ i2 -> send (i1 + i2) $ done)
    (receive $ \ c -> send (ord c) $ done)
