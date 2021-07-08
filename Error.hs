module Error where

import Lexer (Loc)
import Parser (Name,QName)
import Core (Term,Context)

data Error
  = Msg String
  | TypeError Context Loc Term Term Term
  | AnnotError Context Loc Term Term
  | ExpectedFunction Context Loc Term
  | ExpectedSort Context Loc Term
  | InferLambda Context Loc
  
  | UnknownModule Name
  | CircularImports [Name]
  | NameAlreadyDefined Loc QName
  | UndefinedName Loc QName
  | AmbiguousName Loc Name
  
  | DeclWithoutBody Loc
  | BodyWithoutDecl Loc
  
  -- add variable names
  | LinearUnused Loc String
  | LinearUsedAlready Loc String
  | LinearUsedUnrestricted Loc String
  | LinearCase Loc String
  | ErasedUsedRelevant Loc String

  | RefuteNonEmpty Context Loc Term
  | SplitNonData Loc
  | ArityMismatch Loc Int Int -- given, expected
  | ConstructorMismatch Loc String Context Term
  | NonCoveringSplit Loc String
  | IntroNonFunction
  | UnevenPatterns
  
  | InductiveProp Loc
