SOURCE_FILES = Program.fs

.PHONY: clean

kneet.exe : $(SOURCE_FILES)
	fsharpc --out:kneet.exe --target:exe $(SOURCE_FILES) --reference:Microsoft.Z3.dll --reference:kneecap --lib:../kneecap/

clean:
	rm -f kneet.exe
