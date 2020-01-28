/**
 * Copyright (c) 2017-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

const React = require('react');

class Footer extends React.Component {
  docUrl(doc, language) {
    const baseUrl = this.props.config.baseUrl;
    const docsUrl = this.props.config.docsUrl;
    const docsPart = `${docsUrl ? `${docsUrl}/` : ''}`;
    // const langPart = `${language ? `${language}/` : ''}`;
    const langPart = '';
    return `${baseUrl}${docsPart}${langPart}${doc}`;
  }

  pageUrl(doc, language) {
    const baseUrl = this.props.config.baseUrl;
    return baseUrl + (language ? `${language}/` : '') + doc;
  }

  render() {
    return (
      <footer className="nav-footer" id="footer">
        <section className="sitemap">
          <a href={this.props.config.baseUrl} className="nav-home">
            {this.props.config.footerIcon && (
              <img
                src={this.props.config.baseUrl + this.props.config.footerIcon}
                alt={this.props.config.title}
                width="66"
                height="58"
              />
            )}
          </a>
          <div>
            <h5>Docs</h5>
            <a href={this.docUrl('install.html', this.props.language)}>
              Getting Started
            </a>
            <a href={this.docUrl('ocaml-core.html', this.props.language)}>
              Concepts
            </a>
          </div>
          <div>
            <h5>Community</h5>
            <a href="https://github.com/clarus/coq-of-ocaml/issues?q=is%3Aissue+is%3Aopen+sort%3Aupdated-desc+label%3A%22Enhancement+%3Anew%3A%22"
              target="_blank"
              rel="noreferrer noopener">
              Feature requests and proposals
            </a>
            <a href="https://github.com/clarus/coq-of-ocaml/issues?q=is%3Aissue+is%3Aopen+sort%3Aupdated-desc+label%3A%22Bug+%3Abug%3A%22"
              target="_blank"
              rel="noreferrer noopener">
              Issues
            </a>
            <a href="https://gitter.im/clarus/coq-of-ocaml"
              target="_blank"
              rel="noreferrer noopener">
              Chat room
            </a>
            <a href="https://www.nomadic-labs.com/"
              target="_blank"
              rel="noreferrer noopener">
              Nomadic Labs
            </a>
          </div>
          <div>
            <h5>More</h5>
            {/* <a href={`${this.props.config.baseUrl}blog`}>Blog</a> */}
            <a href="https://github.com/clarus/coq-of-ocaml">GitHub</a>
            <a
              className="github-button"
              href={this.props.config.repoUrl}
              data-icon="octicon-star"
              data-count-href="/clarus/coq-of-ocaml/stargazers"
              data-show-count="true"
              data-count-aria-label="# stargazers on GitHub"
              aria-label="Star this project on GitHub">
              Star
            </a>
            {this.props.config.twitterUsername && (
              <div className="social">
                <a
                  href={`https://twitter.com/${this.props.config.twitterUsername}`}
                  className="twitter-follow-button">
                  Follow @{this.props.config.twitterUsername}
                </a>
              </div>
            )}
            {this.props.config.facebookAppId && (
              <div className="social">
                <div
                  className="fb-like"
                  data-href={this.props.config.url}
                  data-colorscheme="dark"
                  data-layout="standard"
                  data-share="true"
                  data-width="225"
                  data-show-faces="false"
                />
              </div>
            )}
          </div>
        </section>

        <section className="copyright">{this.props.config.copyright}</section>
      </footer>
    );
  }
}

module.exports = Footer;
