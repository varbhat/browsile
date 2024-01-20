package main

import (
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
)

type fc struct {
	ListenAddress string
	TLSKeyPath    string
	TLSCertPath   string
	DirPath       string
	SPA           bool
}

func reqLogger(H http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		log.Printf("%s %s %s\n", r.RemoteAddr, r.Method, r.URL)
		H.ServeHTTP(w, r)
	})
}

func main() {
	var Flagconfig fc
	flag.Usage = func() {
		fmt.Fprintf(flag.CommandLine.Output(), "serv is HTTP File/Directory Server\n\n")
		fmt.Fprintf(flag.CommandLine.Output(), "Usage of %s:\n", os.Args[0])

		flag.VisitAll(func(f *flag.Flag) {
			fmt.Fprintf(flag.CommandLine.Output(), " -%-5v   %v\n", f.Name, f.Usage)
		})
		fmt.Fprintf(flag.CommandLine.Output(), " -%-5v   %v\n", "help", "<opt>  Print this Help")
	}

	flag.StringVar(&Flagconfig.ListenAddress, "addr", ":9955", `<addr> Listen Address (Default: ":9955")`)
	flag.StringVar(&Flagconfig.TLSKeyPath, "key", "", "<path> Path to TLS Key (Required for HTTPS)")
	flag.StringVar(&Flagconfig.TLSCertPath, "cert", "", "<path> Path to TLS Certificate (Required for HTTPS)")
	flag.StringVar(&Flagconfig.DirPath, "dir", ".", `<path> Directory to Serve (Default: Current Directory)`)
	flag.Parse()

	if len(flag.Args()) != 0 {
		fmt.Fprintf(flag.CommandLine.Output(), "Invalid Flags Provided: %s\n\n", flag.Args())
		flag.Usage()
		return
	}

	log.Println("Serving on ", Flagconfig.ListenAddress)

	if Flagconfig.TLSCertPath != "" && Flagconfig.TLSKeyPath != "" {
		log.Println("Serving HTTPS with TLS Cert ", Flagconfig.TLSCertPath, " and TLS Key ", Flagconfig.TLSKeyPath)
		log.Fatal(http.ListenAndServeTLS(Flagconfig.ListenAddress, Flagconfig.TLSCertPath, Flagconfig.TLSKeyPath, reqLogger(FileServer(Dir(Flagconfig.DirPath)))))
	} else {
		log.Fatal(http.ListenAndServe(Flagconfig.ListenAddress, reqLogger(FileServer(Dir(Flagconfig.DirPath)))))
	}
}
