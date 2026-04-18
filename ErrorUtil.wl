(* ::Package:: *)

BeginPackage["HOL`Error`"];

holError::usage =
  "holError[tag, msg] or holError[tag, msg, extra] throws a tagged Failure via holErrorTag.";
holErrorTag::usage =
  "Catch tag used by every HOL throw. Top-level scripts should Catch[..., holErrorTag].";
withHOLErrors::usage =
  "withHOLErrors[body] evaluates body and returns its value, or the Failure if a holError was thrown.";
holFailureQ::usage =
  "holFailureQ[x] is True when x is a Failure produced by holError.";

Begin["`Private`"];

SetAttributes[holError, HoldRest];

holError[tag_String, msg_String] := holError[tag, msg, <||>];

holError[tag_String, msg_String, extra_Association] :=
  Throw[
    Failure["HOLError",
      Join[
        <|
          "MessageTemplate" -> "[`tag`] `msg`",
          "MessageParameters" -> <|"tag" -> tag, "msg" -> msg|>,
          "tag" -> tag,
          "msg" -> msg,
          "stack" -> Stack[]
        |>,
        extra
      ]
    ],
    holErrorTag
  ];

SetAttributes[withHOLErrors, HoldFirst];
withHOLErrors[body_] := Catch[body, holErrorTag];

holFailureQ[f_Failure] := AssociationQ[f[[2]]] && KeyExistsQ[f[[2]], "tag"];
holFailureQ[_] := False;

End[];
EndPackage[];
