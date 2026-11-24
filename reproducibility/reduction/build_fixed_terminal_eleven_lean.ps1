$ErrorActionPreference='Stop'
$env:LEAN_PATH=(Get-Location).Path+[IO.Path]::PathSeparator+$env:LEAN_PATH
foreach ($moduleName in @('ActualDyadicSlopeNorm','FixedTerminalFourteenSlope','ActualDyadicSourcePayment')) {
    & lean -o ($moduleName+'.olean') ($moduleName+'.lean') 2>&1 | Set-Content -LiteralPath ($moduleName+'_eleven_dependency_rebuild.log') -Encoding utf8
    if ($LASTEXITCODE -ne 0) { Get-Content -LiteralPath ($moduleName+'_eleven_dependency_rebuild.log') -Tail 12; exit $LASTEXITCODE }
}
& lean FixedTerminalElevenDensity.lean 2>&1 | Tee-Object FixedTerminalElevenDensity_rebuild.log
exit $LASTEXITCODE
