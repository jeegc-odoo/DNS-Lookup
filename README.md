# DNS-Lookup
Python-based tool for retrieving common DNS data like SPF, DKIM, DMARC, MX and CNAME. It also allows testing connections to STMP servers.
## Important notes to Mac users
First time execution will get caught by the Gatekeeper. Don't throw the app away to the trash, just go to System Settings -> Security and Privacy and scroll all the way down to the Security field and allow the app to open. Every time you reinstall the app you must follow the same procedure. 
## What this app can do
This app can:
* Retrieve DNS records such as SPF, DKIM and DMARC.
* Get the domain's MX and CNAME record.
* Give you a summary of the query.
* Test SMTP servers using ping (for simple connection tests), telnet (for connection with address and port) and openssl (to test connection and authentication using credentials).
## Contribution
You can contribute to improve the app by adding features, killing bugs, making the app more efficient and whatever you consider helpful, always under the same rules:
* The app must be always compatible and compiled for Mac, Linux and Windows. You must upload all that plus the source code.
* The information must never be diverted to other places rather than just the target servers and DNS lookup services.
* A technical document must be included explaining the code.
* Of course this is made with AI and of course you can use AI to modify it. Of course you must check what it did.
