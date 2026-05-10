Let me begin with some clarifications.

'SubjectSubsort String      -- ^ a subsort (e.g. "S1")'

This does not declare a subsort but a /set/:
S1 ⊆ S;

A different syntax is used for subsorts, and there is also syntax for quotient sorts and subquotient sorts.

'TagWitnessDecl        -- ^ f_1, f_2, f_res (canonical element witnesses)'

I would not refer to f_1, f_2, and f_res as 'witnesses.' f_1 is 'the first argument', f_2 is 'the second argument' and f_res is 'the function result.'

'  | TagWitnessBounds      -- ^ f_1_min / f_1_max (witness bounds)'

This is basically a way of saying that f_1 has sort S.
axiom f_1_min: (P_Min → (f_1 → S_Min))
axiom f_1_max: (P_Min → (S_Min → f_1))
An alternative way of rendering this would be the following:
axiom f_1_sorting: (IsWithinBounds S_Min S_Min f_1)

'  | TagFunctionFact       -- ^ f_fact (witness biconditional)'

This expresses how the arguments of a function are connected to the function result. So we should maybe call this FunctionConnection instead of FunctionFact.

Let us next consider how there is repetition among the tags. There could be a single 'Fact' tag (although it might be called 'FunctionConnection') instead of the following:
TagFunctionFact       
TagImageFact          
TagProjectionFact     
TagTupleFact          
TagUserFact           
TagInverseFact  

But then there needs to be tags for the following things as well:
     Function
     Image
  Projection
  Tuple
  Inverse

A UserFact is not a FunctionConnection, so that could be its own tag.

I am tacitly assuming here that tags can be combined. So the tag Function could be combined with the tag Image and the tag FunctionConnection. I am not sure what is common in Haskell, but you would use bitwise operations in many other programming languages.

(It can be a matter of taste which tags should be used in a particular case. What is important is to be consistent so that one avoids ending up with situations where what is logically the same thing can be signified in several different ways (perhaps since different programmers chose to use different conventions).)

Now for some further comments on what the tags could be:

'TagSortOrder'

This exists for each sort:

axiom U_ordering: (U_Max → U_Min)
axiom P_ordering: (P_Max → P_Min)
axiom S_ordering: (S_Max → S_Min)
axiom T_ordering: (T_Max → T_Min)
axiom f_dom_ordering: (f_dom_Max → f_dom_Min)
axiom k_dom_ordering: (k_dom_Max → k_dom_Min)

(Note that f#dom and k#dom are sorts.)

The tag could be called something other than 'ordering.' It is about how the upper limit relates to the lower limit.

' ^ S_upper / S_ordering / S_lower / S_lower_min …'

'S_upper' and 'S_lower' are about relating the sort S to other sorts:
axiom S_upper: (U_Max → S_Max)
axiom S_lower: (S_Min → P_Max)

So these do tell you how there is an 'order' between sorts. In this example, S is 'above' P and 'within' U.

These are of the same kind:
axiom U_to_P: (U_Max → P_Max)
axiom P_to_U: (P_Min → U_Min)

In a way, what really 'orders' sorts is when the minimum for one sort is above the maximum for another sort, as in this case:
axiom S_lower: (S_Min → P_Max)

And then you have the axioms that related upper limits for sorts:
axiom S_upper: (U_Max → S_Max)
axiom U_to_P: (U_Max → P_Max)

And the axioms that relate the lower limits for sorts:
axiom P_to_U: (P_Min → U_Min)

'TagFunctionDecl'       
'TagProjectionDecl'
'TagTupleDecl '    
'TagIRDecl '
'TagInverseDecl '

The tag here could be TagDecl.

'  | TagImageFunction      -- ^ f_dir_img, f_inv_img declarations
  | TagImageFact          -- ^ f_dir_img_fact, f_inv_img_fact
  | TagImageAdjunction '

There  could be a TagImage tag. Since image functions are functions, the tag TagFunction should perhaps always be used at the same time.

'  | TagProjectionDecl     -- ^ f_pi_1, f_pi_2 declarations
  | TagProjectionFact     -- ^ f_pi_1_fact (witness biconditional)
  | TagProjectionInvDecl  -- ^ f_pi_1_inv declaration
  | TagProjectionAdjunction -- ^ f_pi_1_adjunction'

There could be a TagProjection tag. Since projection functions are functions, the tag TagFunction should perhaps always be used at the same time. (This answers your question.)

'  | TagTupleDecl          -- ^ f_tuple declaration
  | TagTupleFact          -- ^ f_tuple_fact (witness biconditional)
  | TagTupleInvDecomp     -- ^ f_tuple_inv_decomposition'

There could be a TagTuple tag. Tuple formation functions are functions, so TagFunction should perhaps always be used at the same time.

' | TagIRDecl             -- ^ IR_f declaration
  | TagIRTupleProj        -- ^ IR_f_tuple_with_projections
  | TagIRProjFromTuple    -- ^ IR_f_projections_from_tuple
  | TagIRSeparates        -- ^ IR_f_separates'

There could be a TagIR tag. IR stands for 'Invertible rectagular'. This is a property that sets can have or lack.

'  | TagInverseDecl        -- ^ g_inv declaration
  | TagInverseFact        -- ^ g_inv_fact'

There could be a TagInverse tag. Inverse functions are functions.

'data Subject
  = SubjectGlobal              -- ^ not tied to any single entity (e.g. U/P decls)
  | SubjectSort   String       -- ^ a sort (e.g. "S", "T")
  | SubjectSubsort String      -- ^ a subsort (e.g. "S1")
  | SubjectFunction String     -- ^ a function (e.g. "f", "g", "k")
  | SubjectProjection String Int -- ^ k-th projection of function (e.g. "f" 1)
  deriving (Eq, Ord, Show)'

Perhaps the right way to do things is to have a 'path' to each axiom set. For example,  f_pi_1_adjunction could have the path [(SubjectFunction "f"), (SubjectProjection 1)] and f_pi_1_fact could likewise have the path [(SubjectFunction "f"), (SubjectProjection 1)]. f_image_adjunction could have the path [(SubjectFunction "f"), (SubjectImage)] and k_pi_1_res_min could have the path [(SubjectFunction "k"), (SubjectProjection 1), (SubjectResObject)].