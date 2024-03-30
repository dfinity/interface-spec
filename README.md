# Internet Computer Reference

**A preview of the latest `master` branch can be found [here](https://khsfq-wqaaa-aaaak-qckvq-cai.icp0.io/docs).**

**The latest *released* version can be found [here](https://internetcomputer.org/docs/current/references/ic-interface-spec).**

This repository contains the source files of the Interface Spec, which describes the externally visible behaviour of the Internet Computer.
The language-independent description of this IC interface is available in [ic.did](./spec/_attachments/ic.did).

It used to contain a reference implementation and acceptance test suite; these can now be found at \<https://github.com/dfinity/ic-hs\>.

## About the Interface Spec

This document describes the external interface of the Internet Computer. It is the authoritative source for interface details (request and function names, parameters, encodings). The goal is to have a document that is authoritative, and provides a place and a language to discuss external features of the Internet Computer in a hopefully concrete way. However, this document intentionally does not address _how_ to implement this behavior, and cannot be used as an implementation spec.

## Versioning

The Interface Spec is versioned, using a three-component version like

    0.2.1

Releases from this repository are tagged using a three-component _code
version_ number:

    0.8.1
    ┬ ┬ ┬
    │ │ └ The third component is bumped upon non-breaking changes to the spec.
    │ └ The second component is bumped with a breaking change to the spec
    └ Always zero for now.

Each major spec version has a release branch (e.g. `release-0.8`) that only sees
non-breaking changes and bugfixes. A release branch should typically be “ahead” of all previous release branches.

The `master` branch contains finished designs, but is not directly scheduled
for implementation. It lists version version number `∞`. The reference
implementation on this branch typically does _not_ fully implement the spec. This branch should always be “ahead” of all the release branches.

## Contributing

This repository accepts external contributions, conditioned on acceptance of the [Contributor Lincense Agreement](https://github.com/dfinity/cla/).
