$ErrorActionPreference='Stop'
$env:LEAN_PATH=(Get-Location).Path+[IO.Path]::PathSeparator+$env:LEAN_PATH
foreach ($part in (Get-ChildItem -LiteralPath . -Filter 'FirstMissingTwelveCriticalPart*.lean' | Sort-Object Name)) {
    $moduleName=$part.BaseName
    [System.IO.File]::WriteAllText((Join-Path (Get-Location).Path ($moduleName+'.log')), '')
    & lean -o ($moduleName+'.olean') $part.Name 2>&1 | Set-Content -LiteralPath ($moduleName+'.log') -Encoding utf8
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath ($moduleName+'.log') -Tail 15
        exit $LASTEXITCODE
    }
    Write-Output ($moduleName+' checked')
}
& lean FirstMissingTwelveCriticalCertificate.lean 2>&1 | Tee-Object FirstMissingTwelveCriticalCertificate.log
exit $LASTEXITCODE
