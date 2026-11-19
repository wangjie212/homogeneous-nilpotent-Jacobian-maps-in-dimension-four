param([string]$LeanBin = 'C:\Users\dell\.cache\lean4\lean-4.34.0-windows\bin',
      [string]$DependencyRoot = 'D:\data\Jacobi\quartic_dependence\.lake\packages')
$ErrorActionPreference = 'Stop'
& python (Join-Path $PSScriptRoot 'check.py') --lean-bin $LeanBin --packages $DependencyRoot
exit $LASTEXITCODE
