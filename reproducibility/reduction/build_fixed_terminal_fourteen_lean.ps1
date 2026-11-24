$ErrorActionPreference='Stop'
$env:LEAN_PATH=(Get-Location).Path+[IO.Path]::PathSeparator+$env:LEAN_PATH
& lean -o ActualDyadicSlopeNorm.olean ActualDyadicSlopeNorm.lean 2>&1 | Set-Content -LiteralPath 'ActualDyadicSlopeNorm_dependency_rebuild.log' -Encoding utf8
if ($LASTEXITCODE -ne 0) { Get-Content -LiteralPath 'ActualDyadicSlopeNorm_dependency_rebuild.log' -Tail 12; exit $LASTEXITCODE }
& lean FixedTerminalFourteenSlope.lean 2>&1 | Tee-Object FixedTerminalFourteenSlope_rebuild.log
exit $LASTEXITCODE
