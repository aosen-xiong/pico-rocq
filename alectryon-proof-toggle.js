(function () {
  "use strict";

  function sentenceText(sentence) {
    var input = sentence.querySelector(".alectryon-input");
    return (input ? input.textContent : sentence.textContent).trim();
  }

  function isProofStart(text) {
    return /^Proof\b/.test(text);
  }

  function isProofEnd(text) {
    return /^(Qed|Defined|Admitted)\s*\./.test(text);
  }

  function markProofSentences() {
    var inProof = false;
    document.querySelectorAll(".alectryon-io").forEach(function (block) {
      block.querySelectorAll(".alectryon-sentence").forEach(function (sentence) {
        var text = sentenceText(sentence);
        if (isProofStart(text)) {
          inProof = true;
        }
        if (inProof) {
          sentence.classList.add("alectryon-proof-sentence");
        }
        if (inProof && isProofEnd(text)) {
          inProof = false;
        }
      });
    });
  }

  function installToggle() {
    var root = document.querySelector(".alectryon-root");
    if (!root) {
      return;
    }

    var controls = document.createElement("div");
    controls.className = "project-proof-controls";

    var button = document.createElement("button");
    button.className = "project-proof-toggle";
    button.type = "button";

    var note = document.createElement("span");
    note.className = "project-proof-note";
    note.textContent = "Hides proof scripts between Proof. and Qed./Defined./Admitted.";

    function refresh() {
      var hidden = document.body.classList.contains("proofs-hidden");
      button.textContent = hidden ? "Show proofs" : "Hide proofs";
      button.setAttribute("aria-pressed", hidden ? "true" : "false");
    }

    button.addEventListener("click", function () {
      document.body.classList.toggle("proofs-hidden");
      refresh();
    });

    controls.appendChild(button);
    controls.appendChild(note);

    var banner = root.querySelector(".alectryon-banner");
    if (banner && banner.nextSibling) {
      root.insertBefore(controls, banner.nextSibling);
    } else {
      root.insertBefore(controls, root.firstChild);
    }

    document.body.classList.add("proofs-hidden");
    refresh();
  }

  document.addEventListener("DOMContentLoaded", function () {
    markProofSentences();
    installToggle();
  });
})();
