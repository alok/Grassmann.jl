import * as React from "react";
import { createRoot } from "react-dom/client";
import MultivectorField from "../../../GrassmannViz/multivectorField.js";

const status = document.getElementById("demo-status");
const container = document.getElementById("demo-root");

function reject(message) {
  status.textContent = "The standalone demo could not start.";
  status.classList.add("error");
  const panel = document.createElement("p");
  panel.className = "demo-error";
  panel.textContent = `${message} Use the static fallback linked below.`;
  container.replaceChildren(panel);
}

try {
  const response = await fetch("scene.json", { cache: "no-store" });
  if (!response.ok) {
    throw new Error(`scene request returned HTTP ${response.status}.`);
  }
  const props = await response.json();
  if (props.schemaVersion !== 2 || !Array.isArray(props.frames) || props.frames.length === 0) {
    throw new Error("scene.json does not match multivector-field schema 2.");
  }
  if (!props.frames.every(frame => Array.isArray(frame.samples) && frame.samples.length > 0)) {
    throw new Error("scene.json contains an empty or malformed frame.");
  }
  createRoot(container).render(React.createElement(MultivectorField, props));
  status.textContent = `${props.frames.length} Lean-computed frames loaded; ${props.frames[0].samples.length} samples per frame.`;
  status.classList.add("ready");
} catch (error) {
  reject(error instanceof Error ? error.message : String(error));
}
