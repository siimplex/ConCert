From Coq Require Import String.
From ConCert.Execution Require Import Monads.
From ConCert.Execution Require Import ResultMonad.

Inductive ProgramError :=
| Custom {Error : Type} (e : Error)
| InvalidArgument
| InvalidInstructionData
| InvalidAccountData
| AccountDataTooSmall
| InsufficientFunds
| IncorrectProgramId
| MissingRequiredSignature
| AccountAlreadyInitialized
| UninitializedAccount
| NotEnoughAccountKeys
| AccountBorrowFailed
| MaxSeedLengthExceeded
| InvalidSeeds
| BorshIoError (s : string)
| AccountNotRentExempt
| UnsupportedSysvar
| IllegalOwner
| MaxAccountsDataSizeExceeded
| InvalidRealloc.

Global Instance Monad_result_error : Monad (fun T => result T ProgramError) :=
  {| ret _ t := Ok t;
     bind _ _ mt f :=
     match mt with
     | Ok t => f t
     | Err e => Err e
     end |}.