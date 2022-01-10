use thiserror::Error;

/// types of error that may happen when manipulating a multiverse
///
#[derive(Error, Debug)]
pub enum MultiverseError {
    #[error("Error while interacting with the Persistent storage of the Multiverse")]
    Storage {
        #[from]
        source: sled::Error,
    },

    #[error("Failed to encode/decode an element of the multiverse")]
    Encoding {
        #[from]
        source: serde_json::Error,
    },

    #[error("Entry was not found")]
    NotFound,
}
