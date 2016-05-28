PROTOCOLS = arp.fs etherip.fs ethernet.fs ipv4.fs
SOURCE_FILES = config.fs general.fs expressions.fs interpretation.fs ir_processing.fs z3_translation.fs ir_translation.fs packets.fs pcap.fs $(PROTOCOLS) kneecap.fs

kneecap.dll : $(SOURCE_FILES)
	fsharpc --out:kneecap.dll --target:library $(SOURCE_FILES) --reference:Microsoft.Z3.dll
