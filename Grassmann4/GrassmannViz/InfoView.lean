import GrassmannViz.Scene
import ProofWidgets.Component.HtmlDisplay

/-!
# Offline InfoView renderer for multivector fields

Lean supplies a validated, versioned scene. The embedded component performs
only view work: camera projection, depth sorting, SVG glyph construction, and
interaction.
-/

namespace GrassmannViz

open Lean ProofWidgets Jsx

/-- Local React/SVG component with no external runtime assets. -/
@[widget_module]
def MultivectorFieldWidget : Component MultivectorFieldProps where
  javascript := include_str "." / "multivectorField.js"

private def errorHtml (message : String) : Html :=
  <div style={json% {
      padding: "16px",
      border: "1px solid var(--vscode-inputValidation-errorBorder)",
      borderRadius: "10px",
      background: "var(--vscode-editor-background)"
    }}>
    <b>Lean rejected the multivector-field scene.</b>
    <pre style={json% { whiteSpace: "pre-wrap" }}>{.text message}</pre>
  </div>

/-- Convert validated props into the offline component. -/
def MultivectorFieldProps.toHtml (props : MultivectorFieldProps) : Html :=
  match props.validate with
  | .ok () => Html.ofComponent MultivectorFieldWidget props #[]
  | .error message => errorHtml message

/-- Render either a complete scene or an explicit local error panel. -/
def sceneResultHtml (result : Except String MultivectorFieldProps) : Html :=
  match result with
  | .ok props => props.toHtml
  | .error message => errorHtml message

/-- Ready-to-use default scene for a one-line `#html` command. -/
def defaultSceneHtml : Html :=
  sceneResultHtml defaultScene

end GrassmannViz
