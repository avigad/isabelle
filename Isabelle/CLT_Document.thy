theory CLT_Document
imports
  Probability
  "~~/src/HOL/Library/OptionalSugar"
begin

declare [[show_brackets = false, show_question_marks = false]]

text \<open>
 \DefineSnippet{tendstoadd}{
   @{thm tendsto_add}
 }%EndSnippet
\<close>

end