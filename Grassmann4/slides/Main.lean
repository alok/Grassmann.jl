import VersoSlides
import SFLeanTalk
import Verso.Output.Html

open Verso Output Html
open VersoSlides

def talkCss : CssFile where
  filename := "sflean-talk.css"
  contents := ⟨include_str "talk.css"⟩

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "black"
      highlightTheme := .githubDark
      transition := "fade"
      width := 1600
      height := 900
      margin := 0.055
      controls := true
      progress := true
      slideNumber := false
      hash := true
      center := true
      extraCss := #[talkCss]
      extraHead := #[{{ <link rel="icon" type="image/svg+xml" href="../favicon.svg" /> }}]
      outputDir := "_slides"
    })
    (doc := %doc SFLeanTalk)
