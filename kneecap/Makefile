PROTOCOLS = $(patsubst %,packet_formats/%, arp.fs etherip.fs ethernet.fs ipv4.fs tcp.fs udp.fs)
SOURCE_FILES = AssemblyInfo.fs config.fs general.fs expressions.fs interpretation.fs ir_processing.fs z3_translation.fs ir_translation.fs packets.fs pcap.fs $(PROTOCOLS) kneecap.fs

.PHONY: clean

kneecap.dll : $(SOURCE_FILES)
	fsharpc --out:kneecap.dll --target:library $(SOURCE_FILES) --reference:Microsoft.Z3.dll

clean:
	rm -f kneecap.dll
