<a href="https://github.com/prefix-dev/resolvo/">
    <img src="https://github.com/user-attachments/assets/ccbc2489-3e94-48fd-9f6e-26ac5267b1d1" alt="banner">
</a>

# Resolvo: Fast package resolver written in Rust

![License][license-badge]
[![crates.io][crates-badge]][crates]
[![Build Status][build-badge]][build]
[![Project Chat][chat-badge]][chat-url]
[![Docs][docs-main-badge]][docs-main]

[license-badge]: https://img.shields.io/badge/license-BSD--3--Clause-blue?style=flat-square
[build-badge]: https://img.shields.io/github/actions/workflow/status/mamba-org/resolvo/rust-compile.yml?style=flat-square&branch=main
[build]: https://github.com/mamba-org/resolvo/actions
[chat-badge]: https://img.shields.io/discord/1082332781146800168.svg?label=&logo=discord&logoColor=ffffff&color=7389D8&labelColor=6A7EC2&style=flat-square
[chat-url]: https://discord.gg/kKV8ZxyzY4
[docs-main-badge]: https://img.shields.io/badge/docs-main-yellow.svg?style=flat-square
[docs-main]: https://docs.rs/resolvo
[crates]: https://crates.io/crates/resolvo
[crates-badge]: https://img.shields.io/crates/v/resolvo.svg

Resolvo implements a fast package resolution algorithm based on CDCL SAT solving.

### Projects using `resolvo`

- [`rip`](https://github.com/prefix-dev/rip): An async package resolver and installer for Python PyPI packages
- [`rattler`](https://github.com/mamba-org/rattler): Conda package resolver and installer (non-async)
- [`resolvo-rpm`](https://github.com/prefix-dev/resolvo-rpm): Experimental RPM resolver for Fedora / RedHat / OpenSUSE ... RPM packages
- ... add yours!

## Features

If resolvo is unable to find a solution it outputs a human-readable error message:

```
The following packages are incompatible
├─ bluesky-widgets >=0, <100 can be installed with any of the following options:
│  └─ bluesky-widgets 42 would require
│     └─ suitcase-utils >=0, <54, which can be installed with any of the following options:
│        └─ suitcase-utils 53
└─ suitcase-utils >=54, <100 cannot be installed because there are no viable options:
   └─ suitcase-utils 54, which conflicts with the versions reported above.
```

Resolvo provides a generic interface which allows integrating the solver with a variety of package managers. For instance resolvo is used in [rattler](https://github.com/mamba-org/rattler) and [pixi](https://github.com/prefix-dev/pixi) to solve packages from the conda ecosystem.

Originally resolvo started out as a port/fork of [libsolv](https://github.com/openSUSE/libsolv) but it has since then diverged substantially. However, the same CDCL algorithm based on MiniSats [An Extensible SAT-solver](http://minisat.se/downloads/MiniSat.pdf) is still used underneath. Major differences compared to libsolv are:

* Resolvo does not come with built-in support for several packaging ecosystems but instead provides a generic interface to allow it to be used in different scenarios.
* Resolvo has support for incremental/lazy solving. This allows users to quickly find solutions in ecosystems where retrieving package metadata is expensive.
* Resolvo is considerably faster than libsolv in large complex cases.
* Resolvo can easily be used in multithreaded environments.
* Resolvo provides human-readable error messages out-of-the-box.
* Resolvo optionally provides an async interface to allow concurrent metadata fetching.
* However, Libsolv is more extensive and supports more complex queries.

## Contributing 😍

We would love to have you contribute! 
See the CONTRIBUTION.md for more info. For questions, requests or a casual chat, we are very active on our discord server. 
You can [join our discord server via this link][chat-url].
