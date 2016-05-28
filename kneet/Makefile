SOURCE_FILES = Program.fs

kneecap.dll : $(SOURCE_FILES)
	fsharpc --out:kneet.exe --target:exe $(SOURCE_FILES) --reference:Microsoft.Z3.dll --reference:kneecap --lib:../kneecap/
