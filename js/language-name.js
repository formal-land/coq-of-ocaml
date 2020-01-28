/**
 * Copyright (c) 2017-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// Turn off ESLint for this file because it's sent down to users as-is.
/* eslint-disable */
window.addEventListener('load', function() {
  function language(label) {
    const div = document.createElement('div');
    div.classList.add('languageBadge');
    div.innerHTML = label;
    return div;
  }

  function addLanguage(codeBlockSelector, language) {
    document.querySelectorAll(codeBlockSelector).forEach(function(code) {
      code.parentNode.appendChild(language.cloneNode(true));
    });
  }

  addLanguage('.hljs.language-coq', language('Coq'));
  addLanguage('.hljs.language-ocaml', language('OCaml'));
});
