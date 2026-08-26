
# Proving Correctness of Problem Reductions Using Dafny

This repository contains the Dafny source code accompanying the paper
*Proving Correctness of Problem Reductions Using Dafny*.

The artifact verifies the correctness of several reductions
between decision problems. It does not verify their time complexity.

## Requirements

The examples were verified using **Dafny 4.9.0**.

Dafny 4.9.0 can be installed as a .NET tool on Windows and Linux:

```bash
dotnet tool install --global Dafny --version 4.9.0
```

Check the installed version:

```bash
dafny --version
```

The reported version should be:

```text
4.9.0
```
## Verification on Linux

Verify an individual reduction with:

```bash
dafny verify file.dfy
```

## Verification on Windows

Open PowerShell in the repository directory.

Verify an individual reduction with:

```powershell
dafny verify file.dfy
```

## Expected output

Successful verification ends with a summary similar to:

```text
Dafny program verifier finished with N verified, 0 errors
```

The value of `N` depends on the file being verified. Every complete
reduction should finish with `0 errors`.

